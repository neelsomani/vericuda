"""LineTerm class hierarchy and translator state/terminator types."""

from __future__ import annotations

import dataclasses
import re
import sys
from typing import TYPE_CHECKING, Dict, List, Match, Optional, Tuple

from .ast_expr import Expr, PtrAdd, Var
from .ast_stmt import (
    AssignStmt, AtomicLoadStmt, AtomicStoreStmt, BarrierStmt,
    LoadStmt, Stmt, StoreStmt,
)
from .func_parsers import parse_expr, parse_operand, split_args

if TYPE_CHECKING:
    from .translator import MIRTranslator


# ---------------------------------------------------------------------------
# Translator state


@dataclasses.dataclass
class TranslatorState:
    derived_exprs: Dict[str, Expr]
    ptr_targets: Dict[str, str]
    ordering_bindings: Dict[str, str]

    def copy(self) -> TranslatorState:
        return TranslatorState(
            derived_exprs=dict(self.derived_exprs),
            ptr_targets=dict(self.ptr_targets),
            ordering_bindings=dict(self.ordering_bindings),
        )


# ---------------------------------------------------------------------------
# Terminator types


class Terminator:
    pass


@dataclasses.dataclass
class GotoTerm(Terminator):
    target: str


@dataclasses.dataclass
class ReturnTerm(Terminator):
    pass


@dataclasses.dataclass
class UnreachableTerm(Terminator):
    pass


@dataclasses.dataclass
class SwitchTerm(Terminator):
    cond: Expr
    true_label: str
    false_label: str


# ---------------------------------------------------------------------------
# Helper functions used by statement terms


def expr_for_pointer(name: str, exprs: Dict[str, Expr]) -> Expr:
    return exprs.get(name, Var(name))


def operand_base(token: str) -> Optional[str]:
    token = token.strip()
    if token.startswith("copy ") or token.startswith("move "):
        token = token.split()[1]
    token = token.strip()
    return token if re.fullmatch(r"_[0-9]+", token) else None


def normalize_ordering(token: str) -> str:
    token = token.strip()
    m = re.search(r"Ordering::([A-Za-z]+)$", token)
    if m:
        return m.group(1)
    return token.split("::")[-1]


def ordering_from_token(token: str, bindings: Dict[str, str]) -> str:
    base = operand_base(token)
    if base and base in bindings:
        return bindings[base]
    return normalize_ordering(token)


# ---------------------------------------------------------------------------
# Switch target parsing


def parse_switch_targets(arms: str) -> Tuple[str, str]:
    """Parse switchInt terminator arms and return (false_label, true_label)."""
    false_label: Optional[str] = None
    true_label: Optional[str] = None
    for entry in arms.split(","):
        entry = entry.strip()
        if not entry or ":" not in entry:
            continue
        key, dest = entry.split(":", 1)
        key = key.strip().lower()
        target = dest.strip().split()[0]
        if key in {"0", "false"}:
            if false_label is None:
                false_label = target
            continue
        if key in {"1", "true"}:
            if true_label is None:
                true_label = target
            continue
        if key == "otherwise":
            if false_label is None:
                false_label = target
            elif true_label is None:
                true_label = target
            continue
        if false_label is None:
            false_label = target
        elif true_label is None:
            true_label = target
    if false_label is None or true_label is None:
        raise ValueError("switchInt requires exactly two branches")
    return false_label, true_label


# ---------------------------------------------------------------------------
# LineTerm base class and concrete subclasses


class LineTerm:
    pattern = re.compile(r"(?!)")
    use_search = False

    @classmethod
    def match(cls, line: str) -> Optional[Match[str]]:
        return cls.pattern.search(line) if cls.use_search else cls.pattern.match(line)

    @classmethod
    def parse(
        cls,
        translator: MIRTranslator,
        line: str,
        state: TranslatorState,
        match: Match[str],
    ) -> object:
        raise NotImplementedError

    @classmethod
    def try_parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState
    ) -> Tuple[bool, object]:
        m = cls.match(line)
        if m is None:
            return False, None
        return True, cls.parse(translator, line, state, m)


# --- Terminator terms ---


class SwitchLineTerm(LineTerm):
    pattern = re.compile(r"switchInt\((?P<cond>.+)\)\s*->\s*\[(?P<arms>.+)\];")

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Terminator:
        cond_expr = parse_operand(match.group("cond"))
        false_label, true_label = parse_switch_targets(match.group("arms"))
        return SwitchTerm(cond=cond_expr, true_label=true_label, false_label=false_label)


class ReturnLineTerm(LineTerm):
    pattern = re.compile(r"return;")

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Terminator:
        return ReturnTerm()


class GotoLineTerm(LineTerm):
    pattern = re.compile(r"goto\s*->\s*(?P<label>bb\d+);")
    use_search = True

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Terminator:
        return GotoTerm(target=match.group("label"))


class AssertLineTerm(LineTerm):
    pattern = re.compile(r"assert\(.*\)\s*->\s*\[success:\s*(?P<label>bb\d+)")
    use_search = True

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Terminator:
        return GotoTerm(target=match.group("label"))


class UnreachableLineTerm(LineTerm):
    pattern = re.compile(r"^unreachable;$")

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Terminator:
        return UnreachableTerm()


# --- Effect terms (no stmt produced) ---


class OrderingSetLineTerm(LineTerm):
    pattern = re.compile(
        r"^\s*(?P<dst>_[0-9]+)\s*=\s*(?:core::sync::atomic::Ordering::)?(?P<ord>Acquire|Release|Relaxed|SeqCst|AcqRel|ReleaseAcquire|Consume)\s*;"
    )

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> bool:
        state.ordering_bindings[match.group("dst")] = match.group("ord")
        return True


class CallReturnLineTerm(LineTerm):
    pattern = re.compile(r"->\s*\[return:\s*(?P<label>bb\d+)")
    use_search = True

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Terminator:
        return GotoTerm(target=match.group("label"))


# --- Statement terms ---


class PtrAddStmtTerm(LineTerm):
    pattern = re.compile(
        r"^\s*(?P<dst>_[0-9]+)\s*=\s*(?:core|std)::ptr::(?:mut_ptr|const_ptr)::.*::add\((?P<args>.+)\)"
    )

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Optional[Stmt]:
        dst = match.group("dst")
        args = split_args(match.group("args"))
        if len(args) < 2:
            return None
        base_expr = parse_operand(args[0])
        offset_expr = parse_operand(args[1])
        ptr_expr = PtrAdd(base_expr, offset_expr)
        state.derived_exprs[dst] = ptr_expr
        if isinstance(base_expr, Var) and base_expr.name in state.ptr_targets:
            state.ptr_targets[dst] = state.ptr_targets[base_expr.name]
        return AssignStmt(dst=dst, expr=ptr_expr)


class RefDerefStmtTerm(LineTerm):
    pattern = re.compile(
        r"^\s*(?P<dst>_[0-9]+)\s*=\s*&(?:mut\s+)?\(\*(?P<src>_[0-9]+)\)"
    )

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Stmt:
        dst = match.group("dst")
        src = match.group("src")
        bound = Var(src)
        state.derived_exprs[dst] = bound
        if src in state.ptr_targets:
            state.ptr_targets[dst] = state.ptr_targets[src]
        return AssignStmt(dst=dst, expr=bound)


class RefBindStmtTerm(LineTerm):
    pattern = re.compile(r"^\s*(?P<dst>_[0-9]+)\s*=\s*&(?:mut\s+)?(?P<src>_[0-9]+)")

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Stmt:
        dst = match.group("dst")
        src = match.group("src")
        bound = Var(src)
        state.derived_exprs[dst] = bound
        if src in state.ptr_targets:
            state.ptr_targets[dst] = state.ptr_targets[src]
        return AssignStmt(dst=dst, expr=bound)


class LoadStmtTerm(LineTerm):
    pattern = re.compile(
        r"^\s*(?P<dst>_[0-9]+)\s*=\s*(?:copy|move)\s*\(\*(?P<ptr>_[0-9]+)\)"
    )

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Stmt:
        dst = match.group("dst")
        ptr = match.group("ptr")
        ty_info = translator.types.get(dst)
        mir_ty = ty_info.mir_ty if ty_info and ty_info.mir_ty else "TyU32"
        return LoadStmt(dst=dst, addr=expr_for_pointer(ptr, state.derived_exprs), ty=mir_ty)


class StoreStmtTerm(LineTerm):
    pattern = re.compile(r"^\s*\(\*(?P<ptr>_[0-9]+)\)\s*=\s*(?P<rhs>.+);")

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Stmt:
        ptr = match.group("ptr")
        rhs = match.group("rhs")
        addr_expr = expr_for_pointer(ptr, state.derived_exprs)
        elem_ty = state.ptr_targets.get(ptr, "TyU32")
        return StoreStmt(
            addr=addr_expr,
            value=parse_expr(rhs.rstrip(";"), translator.warnings),
            ty=elem_ty,
        )


class AtomicLoadStmtTerm(LineTerm):
    pattern = re.compile(r"^\s*(?P<dst>_[0-9]+)\s*=\s*AtomicU\d+::load\((?P<args>.+)\)")

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Stmt:
        dst = match.group("dst")
        args = split_args(match.group("args"))
        if len(args) < 2 or ordering_from_token(args[-1], state.ordering_bindings) != "Acquire":
            print(f"error: unsupported atomic load ordering in line: {line}", file=sys.stderr)
            sys.exit(2)
        addr_expr = parse_operand(args[0])
        ty_info = translator.types.get(dst)
        mir_ty = ty_info.mir_ty if ty_info and ty_info.mir_ty else "TyU32"
        return AtomicLoadStmt(dst=dst, addr=addr_expr, ty=mir_ty)


class AtomicStoreStmtTerm(LineTerm):
    pattern = re.compile(r"^\s*(?:_[0-9]+\s*=\s*)?AtomicU\d+::store\((?P<args>.+)\)")

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Stmt:
        args = split_args(match.group("args"))
        if len(args) < 3 or ordering_from_token(args[-1], state.ordering_bindings) != "Release":
            print(f"error: unsupported atomic store ordering in line: {line}", file=sys.stderr)
            sys.exit(2)
        addr_expr = parse_operand(args[0])
        val_expr = parse_expr(args[1], translator.warnings)
        ptr_name = operand_base(args[0])
        ty = state.ptr_targets.get(ptr_name or "", "TyU32")
        return AtomicStoreStmt(addr=addr_expr, value=val_expr, ty=ty)


class AssignStmtTerm(LineTerm):
    pattern = re.compile(r"^\s*(?P<dst>_[0-9]+)\s*=\s*(?P<rhs>.+);")

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Stmt:
        dst = match.group("dst")
        rhs = match.group("rhs").rstrip(";")
        expr = parse_expr(rhs, translator.warnings)
        return AssignStmt(dst=dst, expr=expr)


class BarrierStmtTerm(LineTerm):
    pattern = re.compile(r"barrier|syncthreads", re.IGNORECASE)
    use_search = True

    @classmethod
    def parse(
        cls, translator: MIRTranslator, line: str, state: TranslatorState, match: Match[str]
    ) -> Stmt:
        return BarrierStmt()

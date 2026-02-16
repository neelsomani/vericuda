#!/usr/bin/env python3
"""Translate a restricted MIR dump into a Coq MIR program.

The translator is intentionally small and pattern-driven.  It recognises the
handful of MIR shapes exercised by the MVP kernels (`saxpy`,
`atomic_flag::acquire_release`) and emits the corresponding Gallina terms under
`MIRSyntax`.

Input expectations
------------------
- A single function MIR dump produced by `rustc -Z dump-mir`.
- We only care about loads, stores, atomic acquire/release calls, pointer adds,
  and the occasional barrier call.  Everything else is ignored.

Output
------
- A Coq file defining a module `<ModuleName>` containing `prog : list M.stmt`.
- The ordering of statements matches the order they appear in the MIR dump.

Limitations
-----------
- Regex-driven (no full parser); meant for the two curated kernels only.
- Pointer/base addresses are left symbolic – consumers should provide the
  environment/memory when executing the program inside Coq.
"""

from __future__ import annotations

import argparse
import dataclasses
import pathlib
import re
import sys
from typing import Dict, List, Optional, Sequence, Tuple, Set


# ---------------------------------------------------------------------------
# Small expression AST we render into MIRSyntax terms


class Expr:
    def to_coq(self) -> str:
        raise NotImplementedError


@dataclasses.dataclass
class Var(Expr):
    name: str

    def to_coq(self) -> str:
        return f'M.EVar "{self.name}"'


@dataclasses.dataclass
class Const(Expr):
    ctor: str
    value: str

    def to_coq(self) -> str:
        return f"M.EVal ({self.ctor} {self.value})"


@dataclasses.dataclass
class BoolConst(Expr):
    value: bool

    def to_coq(self) -> str:
        tag = "true" if self.value else "false"
        return f"M.EVal (M.VBool {tag})"


@dataclasses.dataclass
class Add(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.EAdd ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"


@dataclasses.dataclass
class Mul(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.EMul ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"


@dataclasses.dataclass
class PtrAdd(Expr):
    base: Expr
    offset: Expr

    def to_coq(self) -> str:
        return f"M.EPtrAdd ({self.base.to_coq()}) ({self.offset.to_coq()})"


# ---------------------------------------------------------------------------
# Statement representation


class Stmt:
    def to_coq(self) -> str:
        raise NotImplementedError


@dataclasses.dataclass
class LoadStmt(Stmt):
    dst: str
    addr: Expr
    ty: str

    def to_coq(self) -> str:
        return f'M.SLoad "{self.dst}" ({self.addr.to_coq()}) M.{self.ty}'


@dataclasses.dataclass
class StoreStmt(Stmt):
    addr: Expr
    value: Expr
    ty: str

    def to_coq(self) -> str:
        return f'M.SStore ({self.addr.to_coq()}) ({self.value.to_coq()}) M.{self.ty}'


@dataclasses.dataclass
class AtomicLoadStmt(Stmt):
    dst: str
    addr: Expr
    ty: str

    def to_coq(self) -> str:
        return (
            f'M.SAtomicLoadAcquire "{self.dst}" ({self.addr.to_coq()}) M.{self.ty}'
        )


@dataclasses.dataclass
class AtomicStoreStmt(Stmt):
    addr: Expr
    value: Expr
    ty: str

    def to_coq(self) -> str:
        return (
            f'M.SAtomicStoreRelease ({self.addr.to_coq()}) ({self.value.to_coq()}) M.{self.ty}'
        )


@dataclasses.dataclass
class BarrierStmt(Stmt):
    def to_coq(self) -> str:
        return "M.SBarrier"


@dataclasses.dataclass
class IfStmt(Stmt):
    cond: Expr
    then_branch: List[Stmt]
    else_branch: List[Stmt]

    def to_coq(self) -> str:
        return (
            f"M.SIf ({self.cond.to_coq()}) {render_stmt_block(self.then_branch)} "
            f"{render_stmt_block(self.else_branch)}"
        )


@dataclasses.dataclass
class WhileStmt(Stmt):
    cond: Expr
    body: List[Stmt]

    def to_coq(self) -> str:
        return f"M.SWhile ({self.cond.to_coq()}) {render_stmt_block(self.body)}"


def render_stmt_block(stmts: Sequence[Stmt]) -> str:
    if not stmts:
        return "[]"
    inner = ";\n      ".join(stmt.to_coq() for stmt in stmts)
    return f"[ {inner} ]"


# ---------------------------------------------------------------------------
# Type plumbing


@dataclasses.dataclass
class TypeInfo:
    kind: str  # "scalar", "ptr", "ref", "other"
    mir_ty: Optional[str]
    element: Optional[str] = None  # for pointers / refs


TYPE_ALIASES = {
    "usize": "TyU64",
    "isize": "TyI32",
    "i32": "TyI32",
    "u32": "TyU32",
    "f32": "TyF32",
    "bool": "TyBool",
}


def classify_type(raw: str) -> TypeInfo:
    raw = raw.strip()

    # References are treated like pointers for our purposes.
    if raw.startswith("&"):
        elem = raw[1:].strip()
        elem_ty = pointee_type(elem)
        return TypeInfo(kind="ref", mir_ty="TyU64", element=elem_ty)

    if raw.startswith("*const") or raw.startswith("*mut"):
        elem = raw.split(None, 1)[1]
        elem_ty = pointee_type(elem)
        return TypeInfo(kind="ptr", mir_ty="TyU64", element=elem_ty)

    alias = TYPE_ALIASES.get(raw)
    if alias:
        return TypeInfo(kind="scalar", mir_ty=alias)

    # Atomic payloads collapse to u32 for the MVP subset.
    if "AtomicU32" in raw:
        return TypeInfo(kind="other", mir_ty="TyU32")

    return TypeInfo(kind="other", mir_ty=None)


def pointee_type(raw: str) -> str:
    raw = raw.strip()
    if "AtomicU32" in raw:
        return "TyU32"
    alias = TYPE_ALIASES.get(raw)
    return alias or "TyU32"


# ---------------------------------------------------------------------------
# Parsing helpers


IDENT = r"_[0-9A-Za-z]+"

RE_FUNC_HEADER = re.compile(r"^fn\s+\w+\((?P<args>.*)\)\s*->")
RE_LET = re.compile(r"^\s*let(?: mut)?\s+(?P<name>{ident}):\s*(?P<ty>[^;]+);".format(ident=IDENT))
RE_PTR_ADD = re.compile(
    r"^\s*(?P<dst>{ident})\s*=\s*core::ptr::(?:mut_ptr|const_ptr)::.*::add\((?P<args>.+)\)".format(
        ident=IDENT
    )
)
RE_REF_DEREF = re.compile(
    r"^\s*(?P<dst>{ident})\s*=\s*&\(\*(?P<src>{ident})\)".format(ident=IDENT)
)
RE_LOAD = re.compile(
    r"^\s*(?P<dst>{ident})\s*=\s*(?:copy|move)\s*\(\*(?P<ptr>{ident})\)".format(ident=IDENT)
)
RE_STORE = re.compile(
    r"^\s*\(\*(?P<ptr>{ident})\)\s*=\s*(?P<rhs>.+);".format(ident=IDENT)
)
RE_ATOMIC_LOAD = re.compile(
    r"^\s*(?P<dst>{ident})\s*=\s*AtomicU\d+::load\((?P<args>.+)\)".format(ident=IDENT)
)
RE_ATOMIC_STORE = re.compile(
    r"^\s*(?:{ident}\s*=\s*)?AtomicU\d+::store\((?P<args>.+)\)".format(ident=IDENT)
)
RE_BARRIER = re.compile(r"barrier|syncthreads", re.IGNORECASE)
RE_ORDERING_SET = re.compile(
    r"^\s*(?P<dst>{ident})\s*=\s*(?:core::sync::atomic::Ordering::)?(?P<ord>Acquire|Release|Relaxed|SeqCst|AcqRel|ReleaseAcquire|Consume)\s*;".format(
        ident=IDENT
    )
)
RE_BLOCK_START = re.compile(r"^\s*(bb\d+):\s*\{")
RE_SWITCH = re.compile(r"switchInt\((?P<cond>.+)\)\s*->\s*\[(?P<arms>.+)\];")
RE_GOTO = re.compile(r"goto\s*->\s*(?P<label>bb\d+);")
RE_RETURN_TERM = re.compile(r"return;")
RE_ASSERT = re.compile(r"assert\(.*\)\s*->\s*\[success:\s*(?P<label>bb\d+)")
RE_CALL_RETURN = re.compile(r"->\s*\[return:\s*(?P<label>bb\d+)")


@dataclasses.dataclass
class TranslatorState:
    # A class to hold state during translation, such as derived expressions for pointer arithmetic, pointer target types, and ordering bindings.
    derived_exprs: Dict[str, Expr]
    ptr_targets: Dict[str, str]
    ordering_bindings: Dict[str, str]

    def copy(self) -> "TranslatorState":
        return TranslatorState(
            derived_exprs=dict(self.derived_exprs),
            ptr_targets=dict(self.ptr_targets),
            ordering_bindings=dict(self.ordering_bindings),
        )


@dataclasses.dataclass
class Block:
    label: str
    lines: List[str]


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


@dataclasses.dataclass
class LoopContext:
    header_label: str
    exit_label: str
    break_seen: bool = False
    continue_sources: Set[str] = dataclasses.field(default_factory=set)


def split_args(arg_str: str) -> List[str]:
    args: List[str] = []
    depth = 0
    current: List[str] = []
    for ch in arg_str:
        if ch == "," and depth == 0:
            args.append("".join(current).strip())
            current = []
            continue
        if ch == "(":
            depth += 1
        elif ch == ")" and depth > 0:
            depth -= 1
        current.append(ch)
    if current:
        args.append("".join(current).strip())
    return args


def parse_operand(token: str) -> Expr:
    token = token.strip()
    if token.startswith("copy ") or token.startswith("move "):
        return Var(token.split()[1])

    if token.startswith("const "):
        payload = token[len("const "):]
        if payload == "true":
            return BoolConst(True)
        if payload == "false":
            return BoolConst(False)
        m = re.match(r"([-+]?\d+)_([iu](?:32|64)|usize|isize)", payload)
        if m:
            value, suffix = m.groups()
            ctor = {
                "i32": "M.VI32",
                "isize": "M.VI32",
                "u32": "M.VU32",
                "usize": "M.VU64",
                "u64": "M.VU64",
                "i64": "M.VI32",
            }.get(suffix, "M.VI32")
            return Const(ctor=ctor, value=value)
        # Fallback: treat as i32 constant.
        return Const(ctor="M.VI32", value=payload.split("_")[0])

    return Var(token)


def parse_expr(src: str) -> Expr:
    src = src.strip()
    for ctor, cls in ("Add", Add), ("Mul", Mul):
        if src.startswith(f"{ctor}(") and src.endswith(")"):
            inner = src[len(ctor) + 1 : -1]
            args = split_args(inner)
            if len(args) == 2:
                return cls(parse_expr(args[0]), parse_expr(args[1]))
    return parse_operand(src)


# ---------------------------------------------------------------------------
# MIR scanner


def collect_types(lines: Sequence[str]) -> Dict[str, TypeInfo]:
    types: Dict[str, TypeInfo] = {}
    for line in lines:
        line = line.strip()
        m_hdr = RE_FUNC_HEADER.match(line)
        if m_hdr:
            args = m_hdr.group("args")
            if args:
                for raw in split_args(args):
                    raw = raw.strip()
                    if not raw:
                        continue
                    if ":" in raw:
                        name, ty = raw.split(":", 1)
                        name = name.strip()
                        ty = ty.strip()
                        types[name] = classify_type(ty)
            continue

        m_let = RE_LET.match(line)
        if m_let:
            name = m_let.group("name")
            ty = m_let.group("ty")
            types[name] = classify_type(ty)
    return types


def infer_pointer_targets(types: Dict[str, TypeInfo]) -> Dict[str, str]:
    ptrs: Dict[str, str] = {}
    for name, info in types.items():
        if info.kind in {"ptr", "ref"} and info.element:
            ptrs[name] = info.element
    return ptrs


def expr_for_pointer(name: str, exprs: Dict[str, Expr]) -> Expr:
    return exprs.get(name, Var(name))


def operand_base(token: str) -> Optional[str]:
    token = token.strip()
    if token.startswith("copy ") or token.startswith("move "):
        token = token.split()[1]
    # remove possible surrounding parentheses
    token = token.strip()
    return token if re.fullmatch(IDENT, token) else None


def normalize_ordering(token: str) -> str:
    token = token.strip()
    m = re.search(r'Ordering::([A-Za-z]+)$', token)
    if m:
        return m.group(1)
    return token.split("::")[-1]


def ordering_from_token(token: str, bindings: Dict[str, str]) -> str:
    base = operand_base(token)
    if base and base in bindings:
        return bindings[base]
    return normalize_ordering(token)


def strip_control_suffix(line: str) -> str:
    # Remove control flow suffixes like "-> [return: bbN]" to get the underlying statement.
    cleaned = line
    if "->" in cleaned:
        cleaned = cleaned.split("->", 1)[0]
    cleaned = cleaned.rstrip()
    if cleaned and not cleaned.endswith(";"):
        cleaned += ";"
    return cleaned


def split_blocks(lines: Sequence[str]) -> Dict[str, Block]:
    # Split lines into basic blocks. Each block starts with "bbN: {" and ends with "}".
    blocks: Dict[str, Block] = {}
    current_label: Optional[str] = None
    current_lines: List[str] = []
    for raw in lines:
        m_start = RE_BLOCK_START.match(raw)
        if m_start:
            if current_label is not None:
                blocks[current_label] = Block(label=current_label, lines=current_lines)
            current_label = m_start.group(1)
            current_lines = []
            continue
        if current_label is not None and raw.strip() == "}":
            blocks[current_label] = Block(label=current_label, lines=current_lines)
            current_label = None
            current_lines = []
            continue
        if current_label is not None:
            current_lines.append(raw)
    if current_label is not None:
        blocks[current_label] = Block(label=current_label, lines=current_lines)
    return blocks


def parse_switch_targets(arms: str) -> Tuple[str, str]:
    # Parse switchInt terminator arms like "0: bb1, 1: bb2" or "false: bb1, true: bb2" and return the false/true labels.
    false_label: Optional[str] = None
    true_label: Optional[str] = None
    for entry in arms.split(","):
        entry = entry.strip()
        if not entry or ":" not in entry:
            continue
        key, dest = entry.split(":", 1)
        key = key.strip().lower()
        dest = dest.strip()
        target = dest.split()[0]
        if key in {"0", "false"}:
            false_label = target
        elif key in {"1", "true", "otherwise"}:
            true_label = target
        else:
            if false_label is None:
                false_label = target
            else:
                true_label = target
    if false_label is None or true_label is None:
        raise ValueError("switchInt requires exactly two branches")
    return false_label, true_label


class MIRTranslator:
    def __init__(self, lines: Sequence[str]):
        self.lines = lines
        self.types = collect_types(lines)
        self.blocks = split_blocks(lines)
        self._loop_stack: List[LoopContext] = []

    # Loop context helpers -------------------------------------------------
    def _push_loop_context(self, header_label: str, exit_label: str) -> None:
        self._loop_stack.append(LoopContext(header_label=header_label, exit_label=exit_label))

    def _pop_loop_context(self) -> LoopContext:
        return self._loop_stack.pop()

    def _record_loop_flow(self, source: str, target: str) -> None:
        if not self._loop_stack:
            return
        ctx = self._loop_stack[-1]
        if target == ctx.exit_label:
            ctx.break_seen = True
        if target == ctx.header_label:
            ctx.continue_sources.add(source)

    def translate(self) -> List[Stmt]:
        # Start translating from the entry block (bb0 if it exists, otherwise the first block) and follow the control flow until we exhaust reachable blocks or hit unsupported patterns. Collect statements along the way.
        if not self.blocks:
            return []
        entry = "bb0" if "bb0" in self.blocks else next(iter(self.blocks))
        state = TranslatorState(
            derived_exprs={},
            ptr_targets=infer_pointer_targets(self.types),
            ordering_bindings={},
        )
        stmts, _, _ = self._translate_path(entry, state, stop_label=None)
        return stmts

    def _translate_path(
        self,
        label: Optional[str],
        state: TranslatorState,
        stop_label: Optional[str],
        visited: Optional[set] = None,
    ) -> Tuple[List[Stmt], TranslatorState, Optional[str]]:
        # Recursively translate a path of blocks starting from `label` until we hit a terminator that returns or the `stop_label`. Then return the collected statements, final state, and the label that caused us to stop (if any).
        if visited is None:
            visited = set()
        stmts: List[Stmt] = []
        current = label
        while current is not None:
            if stop_label and current == stop_label:
                return stmts, state, stop_label
            if current in visited:
                # raise ValueError(f"loops not supported (stuck in {current})")
                print(f"warning: loops not supported (stuck in {current})", file=sys.stderr)
                return stmts, state, None
            visited.add(current)
            block = self.blocks.get(current)
            if block is None:
                raise ValueError(f"missing block {current}")
            block_stmts, state, terminator = self._process_block(block, state)
            stmts.extend(block_stmts)
            if isinstance(terminator, ReturnTerm):
                return stmts, state, None
            if isinstance(terminator, UnreachableTerm):
                print(f"warning: skipping unreachable block {current}", file=sys.stderr)
                return stmts, state, None
            if isinstance(terminator, GotoTerm):
                current = terminator.target
                continue
            if isinstance(terminator, SwitchTerm):
                if self._translate_loop_if_possible(current, terminator, state, stmts):
                    current = terminator.false_label
                    continue
                true_state = state.copy()
                true_stmts, _, _ = self._translate_path(
                    terminator.true_label,
                    true_state,
                    stop_label=terminator.false_label,
                    visited=set(),
                )
                stmts.append(IfStmt(cond=terminator.cond, then_branch=true_stmts, else_branch=[]))
                current = terminator.false_label
                continue
            raise ValueError("unreachable terminator")
        return stmts, state, None

    def _translate_loop_if_possible(
        self,
        header_label: str,
        terminator: SwitchTerm,
        state: TranslatorState,
        stmts: List[Stmt],
    ) -> bool:
        if not header_label:
            return False
        loop_state = state.copy()
        self._push_loop_context(header_label, terminator.false_label)
        loop_body: List[Stmt] = []
        loop_stop_label: Optional[str] = None
        try:
            loop_body, _, loop_stop_label = self._translate_path(
                terminator.true_label,
                loop_state,
                stop_label=header_label,
                visited=set(),
            )
        finally:
            ctx = self._pop_loop_context()
            if loop_stop_label != header_label:
                return False
            if not ctx.continue_sources:
                return False
            if ctx.break_seen or len(ctx.continue_sources) > 1:
                self._warn_loop_context(header_label, ctx)
                return False
            stmts.append(WhileStmt(cond=terminator.cond, body=loop_body))
            return True

        def _warn_loop_context(self, header_label: str, ctx: LoopContext) -> None:
            if ctx.break_seen:
                print(
                    f"warning: loop starting at {header_label} contains a break; skipping loop translation",
                    file=sys.stderr,
                )
            if len(ctx.continue_sources) > 1:
                print(
                    f"warning: loop starting at {header_label} contains a continue; skipping loop translation",
                    file=sys.stderr,
                )
    def _process_block(
        self, block: Block, state: TranslatorState
    ) -> Tuple[List[Stmt], TranslatorState, Terminator]:
        # Process the statements in a block and identify the terminator. Collect statements along the way and update the state.
        stmts: List[Stmt] = []
        terminator: Optional[Terminator] = None
        for raw in block.lines:
            line = raw.strip()
            if not line or line.startswith("//"):
                continue

            m_switch = RE_SWITCH.match(line)
            if m_switch:
                cond_expr = parse_operand(m_switch.group("cond"))
                false_label, true_label = parse_switch_targets(m_switch.group("arms"))
                terminator = SwitchTerm(cond=cond_expr, true_label=true_label, false_label=false_label)
                continue

            if RE_RETURN_TERM.match(line):
                terminator = ReturnTerm()
                continue

            m_goto = RE_GOTO.search(line)
            if m_goto:
                terminator = GotoTerm(target=m_goto.group("label"))
                self._record_loop_flow(block.label, terminator.target)
                continue

            m_assert = RE_ASSERT.search(line)
            if m_assert:
                terminator = GotoTerm(target=m_assert.group("label"))
                self._record_loop_flow(block.label, terminator.target)
                continue

            if line == "unreachable;":  # panic/unreachable paths, stop translating this branch
                terminator = UnreachableTerm()
                continue

            m_ord = RE_ORDERING_SET.match(line)
            if m_ord:
                state.ordering_bindings[m_ord.group("dst")] = m_ord.group("ord")
                continue

            stmt_line = strip_control_suffix(line)
            stmt = self._parse_statement(stmt_line, state)
            if stmt: stmts.append(stmt)

            m_call = RE_CALL_RETURN.search(line)
            if m_call:
                terminator = GotoTerm(target=m_call.group("label"))
                self._record_loop_flow(block.label, terminator.target)

        return stmts, state, terminator

    def _parse_statement(self, line: str, state: TranslatorState) -> Optional[Stmt]:
        m_ptr_add = RE_PTR_ADD.match(line)
        if m_ptr_add:
            dst = m_ptr_add.group("dst")
            args = split_args(m_ptr_add.group("args"))
            if len(args) >= 2:
                base_expr = parse_operand(args[0])
                offset_expr = parse_operand(args[1])
                state.derived_exprs[dst] = PtrAdd(base_expr, offset_expr)
                if isinstance(base_expr, Var) and base_expr.name in state.ptr_targets:
                    state.ptr_targets[dst] = state.ptr_targets[base_expr.name]
            return None

        m_ref = RE_REF_DEREF.match(line)
        if m_ref:
            dst = m_ref.group("dst")
            src = m_ref.group("src")
            state.derived_exprs[dst] = Var(src)
            if src in state.ptr_targets:
                state.ptr_targets[dst] = state.ptr_targets[src]
            return None

        m_load = RE_LOAD.match(line)
        if m_load:
            dst = m_load.group("dst")
            ptr = m_load.group("ptr")
            ty_info = self.types.get(dst)
            mir_ty = ty_info.mir_ty if ty_info and ty_info.mir_ty else "TyU32"
            return LoadStmt(dst=dst, addr=expr_for_pointer(ptr, state.derived_exprs), ty=mir_ty)

        m_store = RE_STORE.match(line)
        if m_store:
            ptr = m_store.group("ptr")
            rhs = m_store.group("rhs")
            addr_expr = expr_for_pointer(ptr, state.derived_exprs)
            elem_ty = state.ptr_targets.get(ptr, "TyU32")
            return StoreStmt(
                addr=addr_expr,
                value=parse_expr(rhs.rstrip(";")),
                ty=elem_ty,
            )

        m_at_load = RE_ATOMIC_LOAD.match(line)
        if m_at_load:
            dst = m_at_load.group("dst")
            args = split_args(m_at_load.group("args"))
            if len(args) < 2 or ordering_from_token(args[-1], state.ordering_bindings) != "Acquire":
                print(f"error: unsupported atomic load ordering in line: {line}", file=sys.stderr)
                sys.exit(2)
            addr_expr = parse_operand(args[0])
            ty_info = self.types.get(dst)
            mir_ty = ty_info.mir_ty if ty_info and ty_info.mir_ty else "TyU32"
            return AtomicLoadStmt(dst=dst, addr=addr_expr, ty=mir_ty)

        m_at_store = RE_ATOMIC_STORE.match(line)
        if m_at_store:
            args = split_args(m_at_store.group("args"))
            if len(args) < 3 or ordering_from_token(args[-1], state.ordering_bindings) != "Release":
                print(f"error: unsupported atomic store ordering in line: {line}", file=sys.stderr)
                sys.exit(2)
            addr_expr = parse_operand(args[0])
            val_expr = parse_expr(args[1])
            ptr_name = operand_base(args[0])
            ty = state.ptr_targets.get(ptr_name or "", "TyU32")
            return AtomicStoreStmt(addr=addr_expr, value=val_expr, ty=ty)

        if RE_BARRIER.search(line):
            return BarrierStmt()

        return None


# ---------------------------------------------------------------------------
# Rendering


HEADER = """From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

"""


def coq_module(module_name: str, stmts: Sequence[Stmt]) -> str:
    body_lines = [stmt.to_coq() for stmt in stmts]
    prog_body = ";\n    ".join(body_lines) if body_lines else "(* empty *)"
    prog_def = (
        "Definition prog : list M.stmt :=\n  [ "
        + prog_body
        + " ].\n"
        if body_lines
        else "Definition prog : list M.stmt := [].\n"
    )

    return (
        HEADER
        + f"Module {module_name}.\n\n"
        + prog_def
        + "\nEnd "
        + module_name
        + ".\n"
    )


def module_from_path(out_path: pathlib.Path, override: Optional[str]) -> str:
    if override:
        return override
    stem = out_path.stem
    # Capitalise the first letter while preserving underscores.
    if not stem:
        return "Generated"
    return stem[0].upper() + stem[1:]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Translate MIR dump to Coq")
    parser.add_argument("input", type=pathlib.Path, help="Input .mir file")
    parser.add_argument("output", type=pathlib.Path, help="Output .v file")
    parser.add_argument(
        "--module-name",
        dest="module_name",
        help="Override Coq module name (defaults to capitalised output stem)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if not args.input.exists():
        print(f"error: {args.input} does not exist", file=sys.stderr)
        return 1

    lines = args.input.read_text().splitlines()
    translator = MIRTranslator(lines)
    try:
        stmts = translator.translate()
    except ValueError as err:
        print(f"error: {err}", file=sys.stderr)
        return 2

    module_name = module_from_path(args.output, args.module_name)
    coq_src = coq_module(module_name, stmts)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(coq_src)
    print(f"[mir2coq] wrote {args.output} with {len(stmts)} statements")
    return 0


if __name__ == "__main__":
    sys.exit(main())

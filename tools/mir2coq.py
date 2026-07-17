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
  and the occasional barrier call.  Unsupported control flow is diagnosed and
  omitted; unsupported values/types are rejected rather than guessed.

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
from typing import Dict, List, Optional, Sequence, Tuple


class TranslationError(ValueError):
    """The input left the curated MIR fragment and cannot be translated safely."""


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

    # Known control-only/compiler bookkeeping types are recorded but never
    # silently used as memory payloads.
    if (
        raw in {"()", "!", "core::sync::atomic::Ordering"}
        or (raw.startswith("(") and raw.endswith(")"))
    ):
        return TypeInfo(kind="other", mir_ty=None)

    raise TranslationError(f"unsupported MIR type: {raw}")


def pointee_type(raw: str) -> str:
    raw = raw.strip()
    if "AtomicU32" in raw:
        return "TyU32"
    alias = TYPE_ALIASES.get(raw)
    if alias:
        return alias
    raise TranslationError(f"unsupported pointer element type: {raw}")


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
RE_BARRIER = re.compile(r"(?:\bbarrier|\bsyncthreads)\s*\(", re.IGNORECASE)
RE_BASIC_BLOCK = re.compile(r"^bb(?P<block>\d+):\s*\{")
RE_GOTO = re.compile(r"^goto\s*->\s*bb(?P<target>\d+)\s*;")
RE_SWITCH = re.compile(r"^switchInt\s*\(")
RE_ASSERT_TERMINATOR = re.compile(r"^assert\s*\(")
RE_CALL_EDGES = re.compile(r"->\s*\[(?:return|success):")
RE_ORDERING_SET = re.compile(
    r"^\s*(?P<dst>{ident})\s*=\s*(?:core::sync::atomic::Ordering::)?(?P<ord>Acquire|Release|Relaxed|SeqCst|AcqRel|ReleaseAcquire|Consume)\s*;".format(
        ident=IDENT
    )
)


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
        m = re.fullmatch(r"([-+]?\d+)_([iu](?:32|64)|usize|isize)", payload)
        if m:
            value, suffix = m.groups()
            constructors = {
                "i32": "M.VI32",
                "isize": "M.VI32",
                "u32": "M.VU32",
                "usize": "M.VU64",
                "u64": "M.VU64",
            }
            ctor = constructors.get(suffix)
            if ctor is None:
                raise TranslationError(f"unsupported integer constant: {token}")
            return Const(ctor=ctor, value=value)
        raise TranslationError(f"unsupported MIR constant: {token}")

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


def require_mir_type(
    types: Dict[str, TypeInfo], name: str, context: str
) -> str:
    info = types.get(name)
    if info is None or info.mir_ty is None:
        raise TranslationError(
            f"cannot determine supported MIR type for {name} ({context})"
        )
    return info.mir_ty


def parse_statements(
    lines: Sequence[str],
) -> Tuple[List[Stmt], Dict[str, Expr], Dict[str, str], List[str]]:
    types = collect_types(lines)
    ptr_targets = infer_pointer_targets(types)
    derived_exprs: Dict[str, Expr] = {}
    stmts: List[Stmt] = []
    ordering_bindings: Dict[str, str] = {}
    diagnostics: List[str] = []
    current_block: Optional[int] = None

    for line_number, raw in enumerate(lines, start=1):
        # rustc appends comments such as `// scope N at ...` to statements.
        # They are metadata, not part of the statement being matched.
        line = raw.split("//", 1)[0].strip()
        if not line or line.startswith("//"):
            continue

        m_block = RE_BASIC_BLOCK.match(line)
        if m_block:
            current_block = int(m_block.group("block"))
            continue

        m_goto = RE_GOTO.match(line)
        if m_goto:
            target = int(m_goto.group("target"))
            if current_block is not None and target <= current_block:
                diagnostics.append(
                    f"line {line_number}: loop/back-edge bb{current_block} -> "
                    f"bb{target} is not translated; output remains straight-line"
                )
            else:
                diagnostics.append(
                    f"line {line_number}: goto terminator is not translated: {line}"
                )

        if RE_SWITCH.match(line):
            diagnostics.append(
                f"line {line_number}: switchInt terminator is not translated; "
                "branch structure is omitted"
            )
        elif RE_ASSERT_TERMINATOR.match(line):
            diagnostics.append(
                f"line {line_number}: assert terminator is not translated; "
                "success/unwind edges are omitted"
            )
        elif RE_CALL_EDGES.search(line):
            diagnostics.append(
                f"line {line_number}: call return/unwind edges are not translated"
            )

        m_ord = RE_ORDERING_SET.match(line)
        if m_ord:
            ordering_bindings[m_ord.group("dst")] = m_ord.group("ord")
            continue

        # Track pointer expressions first so later loads/stores can reuse them.
        m_ptr_add = RE_PTR_ADD.match(line)
        if m_ptr_add:
            dst = m_ptr_add.group("dst")
            args = split_args(m_ptr_add.group("args"))
            if len(args) >= 2:
                base_expr = parse_operand(args[0])
                offset_expr = parse_operand(args[1])
                derived_exprs[dst] = PtrAdd(base_expr, offset_expr)
                if isinstance(base_expr, Var) and base_expr.name in ptr_targets:
                    ptr_targets[dst] = ptr_targets[base_expr.name]
            continue

        m_ref = RE_REF_DEREF.match(line)
        if m_ref:
            dst = m_ref.group("dst")
            src = m_ref.group("src")
            derived_exprs[dst] = Var(src)
            if src in ptr_targets:
                ptr_targets[dst] = ptr_targets[src]
            continue

        m_load = RE_LOAD.match(line)
        if m_load:
            dst = m_load.group("dst")
            ptr = m_load.group("ptr")
            mir_ty = require_mir_type(types, dst, "load destination")
            stmts.append(LoadStmt(dst=dst, addr=expr_for_pointer(ptr, derived_exprs), ty=mir_ty))
            continue

        m_store = RE_STORE.match(line)
        if m_store:
            ptr = m_store.group("ptr")
            rhs = m_store.group("rhs")
            addr_expr = expr_for_pointer(ptr, derived_exprs)
            elem_ty = ptr_targets.get(ptr)
            if elem_ty is None:
                raise TranslationError(
                    f"cannot determine pointer element type for store through {ptr}"
                )
            stmts.append(
                StoreStmt(
                    addr=addr_expr,
                    value=parse_expr(rhs.rstrip(";")),
                    ty=elem_ty,
                )
            )
            continue

        m_at_load = RE_ATOMIC_LOAD.match(line)
        if m_at_load:
            dst = m_at_load.group("dst")
            args = split_args(m_at_load.group("args"))
            if len(args) < 2 or ordering_from_token(args[-1], ordering_bindings) != "Acquire":
                raise TranslationError(
                    f"unsupported atomic load ordering in line: {line}"
                )
            addr_expr = parse_operand(args[0])
            mir_ty = require_mir_type(types, dst, "atomic load destination")
            stmts.append(AtomicLoadStmt(dst=dst, addr=addr_expr, ty=mir_ty))
            continue

        m_at_store = RE_ATOMIC_STORE.match(line)
        if m_at_store:
            args = split_args(m_at_store.group("args"))
            if len(args) < 3 or ordering_from_token(args[-1], ordering_bindings) != "Release":
                raise TranslationError(
                    f"unsupported atomic store ordering in line: {line}"
                )
            addr_expr = parse_operand(args[0])
            val_expr = parse_expr(args[1])
            ptr_name = operand_base(args[0])
            ty = ptr_targets.get(ptr_name or "")
            if ty is None:
                raise TranslationError(
                    f"cannot determine atomic pointer element type in line: {line}"
                )
            stmts.append(
                AtomicStoreStmt(
                    addr=addr_expr,
                    value=val_expr,
                    ty=ty,
                )
            )
            continue

        if RE_BARRIER.search(line):
            stmts.append(BarrierStmt())

    return stmts, derived_exprs, ptr_targets, diagnostics


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
    try:
        stmts, _, _, diagnostics = parse_statements(lines)
    except TranslationError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    for diagnostic in diagnostics:
        print(f"[mir2coq] WARNING: {diagnostic}", file=sys.stderr)

    module_name = module_from_path(args.output, args.module_name)
    coq_src = coq_module(module_name, stmts)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(coq_src)
    print(f"[mir2coq] wrote {args.output} with {len(stmts)} statements")
    return 0


if __name__ == "__main__":
    sys.exit(main())

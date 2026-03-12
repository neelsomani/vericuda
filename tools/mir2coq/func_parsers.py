"""Function-call parsers and expression parsing helpers."""

from __future__ import annotations

import dataclasses
import re
import struct
from typing import Dict, List, Optional

from .ast_expr import (
    Add, BitAnd, BitXor, BoolConst, Const, CudaVar, Div, Eq, Expr,
    Lt, Mul, Not, PtrAdd, Rem, Shl, Shr, Sub, SymbolConst, Var,
    format_z_literal,
)
from .types import CUDA_INTRINSICS, SYMBOLIC_CONSTS


# ---------------------------------------------------------------------------
# Low-level string helpers


def split_args(arg_str: str) -> List[str]:
    """Split a comma-separated argument list respecting parenthesis nesting."""
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


def strip_wrapped_parens(token: str) -> str:
    stripped = token.strip()
    while stripped.startswith("(") and stripped.endswith(")"):
        depth = 0
        balanced = True
        for idx, ch in enumerate(stripped):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and idx != len(stripped) - 1:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        stripped = stripped[1:-1].strip()
    return stripped


def normalize_symbol_token(token: str) -> str:
    cleaned = token.strip()
    while cleaned and cleaned[-1] in ":;,":
        cleaned = cleaned[:-1].rstrip()
    return cleaned


def symbol_const_name(payload: str) -> Optional[str]:
    cleaned = normalize_symbol_token(payload)
    return SYMBOLIC_CONSTS.get(cleaned)


# ---------------------------------------------------------------------------
# Operand / expression parsers


def parse_operand(token: str) -> Expr:
    token = token.strip()
    if token.startswith("copy ") or token.startswith("move "):
        remainder = token.split(None, 1)[1]
        return parse_operand(remainder)

    token = strip_wrapped_parens(token)

    if token.startswith("const "):
        payload = token[len("const "):]
        if payload == "true":
            return BoolConst(True)
        if payload == "false":
            return BoolConst(False)
        m_float = re.match(r"([-+]?\d+(?:\.\d+)?)(?:f32)", payload)
        if m_float:
            numeric = float(m_float.group(1))
            bits = struct.unpack("<I", struct.pack("<f", numeric))[0]
            return Const(ctor="M.VF32", value=str(bits))
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
        sym = symbol_const_name(payload)
        if sym:
            return SymbolConst(name=sym)
        return Const(ctor="M.VI32", value=payload.split("_")[0])

    m_cast = re.match(r"^(?P<base>_[0-9]+)\s+as\s+.+", token)
    if m_cast:
        return Var(m_cast.group("base"))

    m_field = re.match(r"^(?P<name>_[0-9]+)\.(?P<field>\d+):", token)
    if m_field:
        base = m_field.group("name")
        field = m_field.group("field")
        if field == "0":
            return Var(base)
        if field == "1":
            return BoolConst(False)

    return Var(token)


# ---------------------------------------------------------------------------
# Function-call AST and parsers


@dataclasses.dataclass
class FuncCall:
    name: str
    args: List[str]
    raw: str


class LibFuncParser:
    def match(self, call: FuncCall) -> bool:
        raise NotImplementedError

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        raise NotImplementedError


@dataclasses.dataclass
class NamedBinaryParser(LibFuncParser):
    name: str
    expr_cls: type

    def match(self, call: FuncCall) -> bool:
        return call.name == self.name

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        if len(call.args) != 2:
            return None
        return self.expr_cls(
            parse_expr(call.args[0], warnings), parse_expr(call.args[1], warnings)
        )


class NamedUnaryParser(LibFuncParser):
    def __init__(self, name: str, ctor):
        self.name = name
        self.ctor = ctor

    def match(self, call: FuncCall) -> bool:
        return call.name == self.name

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        if len(call.args) != 1:
            return None
        return self.ctor(parse_expr(call.args[0], warnings))


class IteratorNextParser(LibFuncParser):
    def match(self, call: FuncCall) -> bool:
        return call.name.endswith("::next")

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        if not call.args:
            return None
        return parse_expr(call.args[0], warnings)


@dataclasses.dataclass
class SuffixBinaryParser(LibFuncParser):
    """Matches call names by suffix; maps to a binary expr class."""
    suffix: str
    expr_cls: type

    def match(self, call: FuncCall) -> bool:
        return call.name.endswith(self.suffix)

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        if len(call.args) != 2:
            return None
        return self.expr_cls(
            parse_expr(call.args[0], warnings), parse_expr(call.args[1], warnings)
        )


@dataclasses.dataclass
class NamedRewriteParser(LibFuncParser):
    name: str

    def match(self, call: FuncCall) -> bool:
        return call.name == self.name

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        if len(call.args) != 2:
            return None
        lhs = parse_expr(call.args[0], warnings)
        rhs = parse_expr(call.args[1], warnings)
        if self.name == "Ge":
            return Not(Lt(lhs, rhs))
        if self.name == "Ne":
            return Not(Eq(lhs, rhs))
        return None


@dataclasses.dataclass
class NamedUnaryIdentityParser(LibFuncParser):
    name: str

    def match(self, call: FuncCall) -> bool:
        return call.name == self.name

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        if len(call.args) != 1:
            return None
        return parse_expr(call.args[0], warnings)


@dataclasses.dataclass
class UndefFunctionParser(LibFuncParser):
    """Maps functions with undefined/opaque semantics to a fixed return value."""
    name_fragment: str
    ret: Expr

    def match(self, call: FuncCall) -> bool:
        return self.name_fragment in call.name

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        warnings.append(f"[undef] {call.name} treated as {self.ret.to_coq()}")
        return self.ret


class CudaIntrinsicParser(LibFuncParser):
    """Maps zero-argument CUDA built-in reads to CudaVar symbolic inputs."""

    @staticmethod
    def _bare_name(call: FuncCall) -> Optional[str]:
        bare = call.name.split("::")[-1]
        return bare if bare in CUDA_INTRINSICS else None

    def match(self, call: FuncCall) -> bool:
        return self._bare_name(call) is not None

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        return CudaVar(self._bare_name(call))


@dataclasses.dataclass
class TypeConstParser(LibFuncParser):
    name: str
    prefix: str

    def match(self, call: FuncCall) -> bool:
        return call.name == self.name

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        if len(call.args) != 1:
            return None
        ty = call.args[0].strip().replace(" ", "")
        if ty == "u128":
            return SymbolConst(name=f"{self.prefix}_u128")
        return None


class IdentityFuncParser(LibFuncParser):
    def __init__(self, suffix: str):
        self.suffix = suffix

    def match(self, call: FuncCall) -> bool:
        return call.name.endswith(self.suffix)

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        if len(call.args) != 1:
            return None
        return parse_expr(call.args[0], warnings)


class OpaqueFuncParser(LibFuncParser):
    def __init__(self, predicate):
        self.predicate = predicate

    def match(self, call: FuncCall) -> bool:
        return self.predicate(call.name)

    def parse(self, call: FuncCall, warnings: List[str]) -> Optional[Expr]:
        return None


FUNC_PARSERS: List[LibFuncParser] = [
    CudaIntrinsicParser(),
    UndefFunctionParser("assert_kernel_parameter_is_copy", BoolConst(True)),
    NamedBinaryParser("AddWithOverflow", Add),
    NamedBinaryParser("MulWithOverflow", Mul),
    NamedUnaryParser("discriminant", lambda arg: arg),
    IteratorNextParser(),
    IdentityFuncParser("::into_iter"),
    NamedUnaryIdentityParser("PtrMetadata"),
    TypeConstParser("AlignOf", "ALIGNOF"),
    TypeConstParser("SizeOf", "SIZEOF"),
    NamedRewriteParser("Ge"),
    NamedRewriteParser("Ne"),
    NamedBinaryParser("Add", Add),
    NamedBinaryParser("Sub", Sub),
    NamedBinaryParser("Mul", Mul),
    NamedBinaryParser("Div", Div),
    NamedBinaryParser("Rem", Rem),
    NamedBinaryParser("Lt", Lt),
    NamedBinaryParser("Eq", Eq),
    NamedBinaryParser("BitAnd", BitAnd),
    NamedBinaryParser("BitXor", BitXor),
    SuffixBinaryParser("::wrapping_add", Add),
    SuffixBinaryParser("::wrapping_sub", Sub),
    SuffixBinaryParser("::wrapping_mul", Mul),
    SuffixBinaryParser("::wrapping_shl", Shl),
    SuffixBinaryParser("::wrapping_shr", Shr),
    NamedUnaryParser("Not", Not),
]


def parse_func_call(src: str) -> Optional[FuncCall]:
    token = src.strip()
    if not token.endswith(")"):
        return None
    l_paren = token.find("(")
    if l_paren <= 0:
        return None
    name = token[:l_paren].strip()
    if not name:
        return None
    depth = 0
    for ch in token[l_paren:]:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                return None
    if depth != 0:
        return None
    inner = token[l_paren + 1: -1]
    args = split_args(inner) if inner.strip() else []
    return FuncCall(name=name, args=args, raw=token)


def parse_func(src: str, warnings: List[str]) -> Optional[Expr]:
    call = parse_func_call(src)
    if call is None:
        return None
    for parser in FUNC_PARSERS:
        if parser.match(call):
            parsed = parser.parse(call, warnings)
            if parsed is not None:
                return parsed
    return None


def parse_expr(src: str, warnings: Optional[List[str]] = None) -> Expr:
    if warnings is None:
        warnings = []
    token = src.strip()
    normalized = token
    if normalized.startswith("copy ") or normalized.startswith("move "):
        normalized = normalized.split(None, 1)[1].strip()
    normalized = strip_wrapped_parens(normalized)
    m_some = re.match(r"^\(?(?P<base>_[0-9]+)\s+as\s+Some\)?\.0:\s+.+$", normalized)
    if m_some:
        return Var(m_some.group("base"))
    parsed = parse_func(token, warnings)
    if parsed is not None:
        return parsed
    return parse_operand(token)

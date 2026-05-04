"""Expression AST nodes for MIR → Coq translation."""

from __future__ import annotations

import dataclasses
import re
import struct


class Expr:
    def to_coq(self) -> str:
        raise NotImplementedError

    def has_unresolved_expr(self) -> bool:
        return False


def format_z_literal(raw: str) -> str:
    literal = raw.strip()
    if literal.startswith("-") and not literal.startswith("(-"):
        return f"({literal})"
    return literal


@dataclasses.dataclass
class Var(Expr):
    name: str

    def to_coq(self) -> str:
        return f'M.EVar "{self.name}"'

    def has_unresolved_expr(self) -> bool:
        return re.fullmatch(r"_[0-9]+", self.name) is None


@dataclasses.dataclass
class Const(Expr):
    ctor: str
    value: str

    def to_coq(self) -> str:
        literal = format_z_literal(self.value)
        return f"M.EVal ({self.ctor} {literal})"


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

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class Sub(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.ESub ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class Mul(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.EMul ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class Div(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.EDiv ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class Rem(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.ERem ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class Lt(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.ELt ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class Eq(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.EEq ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class BitAnd(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.EAnd ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class BitXor(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.EXor ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class Shl(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.EShl ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class Shr(Expr):
    lhs: Expr
    rhs: Expr

    def to_coq(self) -> str:
        return f"M.EShr ({self.lhs.to_coq()}) ({self.rhs.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.lhs.has_unresolved_expr() or self.rhs.has_unresolved_expr()


@dataclasses.dataclass
class Not(Expr):
    arg: Expr

    def to_coq(self) -> str:
        return f"M.ENot ({self.arg.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.arg.has_unresolved_expr()


@dataclasses.dataclass
class PtrAdd(Expr):
    base: Expr
    offset: Expr

    def to_coq(self) -> str:
        return f"M.EPtrAdd ({self.base.to_coq()}) ({self.offset.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.base.has_unresolved_expr() or self.offset.has_unresolved_expr()


@dataclasses.dataclass
class RangeExpr(Expr):
    start: Expr
    end: Expr

    def to_coq(self) -> str:
        return f"M.ERange ({self.start.to_coq()}) ({self.end.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.start.has_unresolved_expr() or self.end.has_unresolved_expr()


@dataclasses.dataclass
class StepByExpr(Expr):
    iterator: Expr
    step: Expr

    def to_coq(self) -> str:
        return f"M.EStepBy ({self.iterator.to_coq()}) ({self.step.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.iterator.has_unresolved_expr() or self.step.has_unresolved_expr()


@dataclasses.dataclass
class NextExpr(Expr):
    iterator: Expr

    def to_coq(self) -> str:
        return f"M.ENext ({self.iterator.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.iterator.has_unresolved_expr()


@dataclasses.dataclass
class DiscriminantExpr(Expr):
    arg: Expr

    def to_coq(self) -> str:
        return f"M.EDiscriminant ({self.arg.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.arg.has_unresolved_expr()


@dataclasses.dataclass
class OptionGetExpr(Expr):
    arg: Expr

    def to_coq(self) -> str:
        return f"M.EOptionGet ({self.arg.to_coq()})"

    def has_unresolved_expr(self) -> bool:
        return self.arg.has_unresolved_expr()


@dataclasses.dataclass
class SymbolConst(Expr):
    name: str

    def to_coq(self) -> str:
        return f"M.EVal (MC.const_{self.name})"


@dataclasses.dataclass
class CudaVar(Expr):
    """A CUDA intrinsic input (block_dim_x, thread_idx_y, …).

    Treated as a symbolic variable whose value is supplied by the environment.
    """
    name: str

    def to_coq(self) -> str:
        return f'M.EVar "CUDA_{self.name}"'

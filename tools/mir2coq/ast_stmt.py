"""Statement AST nodes for MIR → Coq translation."""

from __future__ import annotations

import dataclasses
from typing import List, Sequence

from .ast_expr import Expr


class Stmt:
    def to_coq(self) -> str:
        raise NotImplementedError

    def has_unresolved_expr(self) -> bool:
        return False


def render_stmt_block(stmts: Sequence[Stmt]) -> str:
    if not stmts:
        return "[]"
    inner = ";\n      ".join(stmt.to_coq() for stmt in stmts)
    return f"[ {inner} ]"


@dataclasses.dataclass
class AssignStmt(Stmt):
    dst: str
    expr: Expr

    def to_coq(self) -> str:
        return f'M.SAssign "{self.dst}" ({self.expr.to_coq()})'

    def has_unresolved_expr(self) -> bool:
        return self.expr.has_unresolved_expr()


@dataclasses.dataclass
class LoadStmt(Stmt):
    dst: str
    addr: Expr
    ty: str

    def to_coq(self) -> str:
        return f'M.SLoad "{self.dst}" ({self.addr.to_coq()}) M.{self.ty}'

    def has_unresolved_expr(self) -> bool:
        return self.addr.has_unresolved_expr()


@dataclasses.dataclass
class StoreStmt(Stmt):
    addr: Expr
    value: Expr
    ty: str

    def to_coq(self) -> str:
        return f'M.SStore ({self.addr.to_coq()}) ({self.value.to_coq()}) M.{self.ty}'

    def has_unresolved_expr(self) -> bool:
        return self.addr.has_unresolved_expr() or self.value.has_unresolved_expr()


@dataclasses.dataclass
class AtomicLoadStmt(Stmt):
    dst: str
    addr: Expr
    ty: str

    def to_coq(self) -> str:
        return (
            f'M.SAtomicLoadAcquire "{self.dst}" ({self.addr.to_coq()}) M.{self.ty}'
        )

    def has_unresolved_expr(self) -> bool:
        return self.addr.has_unresolved_expr()


@dataclasses.dataclass
class AtomicStoreStmt(Stmt):
    addr: Expr
    value: Expr
    ty: str

    def to_coq(self) -> str:
        return (
            f'M.SAtomicStoreRelease ({self.addr.to_coq()}) ({self.value.to_coq()}) M.{self.ty}'
        )

    def has_unresolved_expr(self) -> bool:
        return self.addr.has_unresolved_expr() or self.value.has_unresolved_expr()


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

    def has_unresolved_expr(self) -> bool:
        if self.cond.has_unresolved_expr():
            return True
        return any(s.has_unresolved_expr() for s in self.then_branch) or any(
            s.has_unresolved_expr() for s in self.else_branch
        )


@dataclasses.dataclass
class LoopStmt(Stmt):
    body: List[Stmt]

    def to_coq(self) -> str:
        return f"M.SLoop {render_stmt_block(self.body)}"

    def has_unresolved_expr(self) -> bool:
        return any(s.has_unresolved_expr() for s in self.body)


@dataclasses.dataclass
class WhileStmt(Stmt):
    cond: Expr
    body: List[Stmt]

    def to_coq(self) -> str:
        return f"M.SWhile ({self.cond.to_coq()}) {render_stmt_block(self.body)}"

    def has_unresolved_expr(self) -> bool:
        if self.cond.has_unresolved_expr():
            return True
        return any(s.has_unresolved_expr() for s in self.body)

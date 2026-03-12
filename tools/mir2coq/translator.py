"""MIRTranslator: traverses the block CFG and emits a flat list of Stmts."""

from __future__ import annotations

import sys
from typing import Dict, List, Optional, Sequence, Set, Tuple

from .ast_stmt import IfStmt, Stmt, WhileStmt
from .line_terms import (
    AssertLineTerm,
    AssignStmtTerm,
    AtomicLoadStmtTerm,
    AtomicStoreStmtTerm,
    BarrierStmtTerm,
    CallReturnLineTerm,
    GotoLineTerm,
    GotoTerm,
    LineTerm,
    LoadStmtTerm,
    OrderingSetLineTerm,
    PtrAddStmtTerm,
    RefBindStmtTerm,
    RefDerefStmtTerm,
    ReturnLineTerm,
    ReturnTerm,
    StoreStmtTerm,
    SwitchLineTerm,
    SwitchTerm,
    Terminator,
    TranslatorState,
    UnreachableLineTerm,
    UnreachableTerm,
)
from .scanner import (
    Block,
    collect_types,
    infer_pointer_targets,
    split_blocks,
    strip_control_suffix,
)
from .types import TypeInfo


class LoopBoundary(Exception):
    def __init__(self, label: str):
        super().__init__(label)
        self.label = label


class MIRTranslator:
    def __init__(self, lines: Sequence[str]):
        self.lines = lines
        self.types: Dict[str, TypeInfo] = collect_types(lines)
        self.blocks: Dict[str, Block] = split_blocks(lines)
        self._loop_headers_in_progress: Set[str] = set()
        self.warnings: List[str] = []

    def translate(self) -> List[Stmt]:
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
        if visited is None:
            visited = set()
        stmts: List[Stmt] = []
        current = label
        try:
            while current is not None:
                if stop_label and current == stop_label:
                    return stmts, state, stop_label
                if (
                    self._loop_headers_in_progress
                    and current in self._loop_headers_in_progress
                    and (not stop_label or current != stop_label)
                ):
                    raise LoopBoundary(current)
                if current in visited:
                    print(
                        f"warning: loops not supported (stuck in {current})",
                        file=sys.stderr,
                    )
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
                    stmts.append(
                        IfStmt(cond=terminator.cond, then_branch=true_stmts, else_branch=[])
                    )
                    current = terminator.false_label
                    continue
                raise ValueError("unreachable terminator")
        except LoopBoundary as boundary:
            if stop_label and boundary.label == stop_label:
                return stmts, state, stop_label
            raise
        return stmts, state, None

    def _translate_loop_if_possible(
        self,
        header_label: str,
        terminator: SwitchTerm,
        state: TranslatorState,
        stmts: List[Stmt],
    ) -> bool:
        if not header_label or header_label in self._loop_headers_in_progress:
            return False
        loop_state = state.copy()
        self._loop_headers_in_progress.add(header_label)
        try:
            try:
                loop_body, _, loop_stop_label = self._translate_path(
                    terminator.true_label,
                    loop_state,
                    stop_label=header_label,
                    visited=set(),
                )
            except LoopBoundary:
                return False
            if loop_stop_label != header_label:
                return False
            stmts.append(WhileStmt(cond=terminator.cond, body=loop_body))
            return True
        finally:
            self._loop_headers_in_progress.discard(header_label)

    def _try_terms(
        self, line: str, terms: Sequence[type], state: TranslatorState
    ) -> Tuple[bool, object]:
        for term in terms:
            matched, result = term.try_parse(self, line, state)
            if matched:
                return True, result
        return False, None

    def _pre_statement_terminator_rules(self) -> Sequence[type]:
        return (
            SwitchLineTerm,
            ReturnLineTerm,
            GotoLineTerm,
            AssertLineTerm,
            UnreachableLineTerm,
        )

    def _line_effect_rules(self) -> Sequence[type]:
        return (OrderingSetLineTerm,)

    def _post_statement_terminator_rules(self) -> Sequence[type]:
        return (CallReturnLineTerm,)

    def _statement_rules(self) -> Sequence[type]:
        return (
            PtrAddStmtTerm,
            RefDerefStmtTerm,
            RefBindStmtTerm,
            LoadStmtTerm,
            StoreStmtTerm,
            AtomicLoadStmtTerm,
            AtomicStoreStmtTerm,
            AssignStmtTerm,
            BarrierStmtTerm,
        )

    def _process_block(
        self, block: Block, state: TranslatorState
    ) -> Tuple[List[Stmt], TranslatorState, Terminator]:
        stmts: List[Stmt] = []
        terminator: Optional[Terminator] = None
        for raw in block.lines:
            line = raw.strip()
            if not line or line.startswith("//"):
                continue

            matched, result = self._try_terms(line, self._pre_statement_terminator_rules(), state)
            if matched:
                terminator = result
                continue

            matched, _ = self._try_terms(line, self._line_effect_rules(), state)
            if matched:
                continue

            stmt_line = strip_control_suffix(line)
            stmt = self._parse_statement(stmt_line, state)
            if stmt:
                if stmt.has_unresolved_expr():
                    self.warnings.append(
                        f"[{block.label}] parse failed (non _<digits> variable or unsupported expr): {stmt_line}"
                    )
                    stmt = None
                if stmt:
                    stmts.append(stmt)
            else:
                self.warnings.append(f"[{block.label}] unparsed statement: {stmt_line}")

            matched, result = self._try_terms(
                line, self._post_statement_terminator_rules(), state
            )
            if matched:
                terminator = result

        return stmts, state, terminator

    def _parse_statement(self, line: str, state: TranslatorState) -> Optional[Stmt]:
        matched, result = self._try_terms(line, self._statement_rules(), state)
        if not matched:
            return None
        return result if isinstance(result, Stmt) else None

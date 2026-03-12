"""Coq source rendering."""

from __future__ import annotations

import pathlib
from typing import Optional, Sequence

from .ast_stmt import Stmt


HEADER = """From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

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
    if not stem:
        return "Generated"
    return stem[0].upper() + stem[1:]


def warning_log_path(out_path: pathlib.Path) -> pathlib.Path:
    return pathlib.Path("log") / f"{out_path.stem}.log"

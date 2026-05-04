"""MIR source scanning: type collection, block splitting, and related utilities."""

from __future__ import annotations

import dataclasses
import re
from typing import Dict, Optional, Sequence

from .ast_expr import Expr, Var
from .func_parsers import split_args
from .types import TypeInfo, classify_type


@dataclasses.dataclass
class Block:
    label: str
    lines: list[str]


def collect_types(lines: Sequence[str]) -> Dict[str, TypeInfo]:
    types: Dict[str, TypeInfo] = {}
    for line in lines:
        line = line.strip()
        m_hdr = re.match(r"^fn\s+\w+\((?P<args>.*)\)\s*->", line)
        if m_hdr:
            args = m_hdr.group("args")
            if args:
                for raw in split_args(args):
                    raw = raw.strip()
                    if not raw:
                        continue
                    if ":" in raw:
                        name, ty = raw.split(":", 1)
                        types[name.strip()] = classify_type(ty.strip())
            continue
        m_let = re.match(r"^\s*let(?: mut)?\s+(?P<name>_[0-9]+):\s*(?P<ty>[^;]+);", line)
        if m_let:
            types[m_let.group("name")] = classify_type(m_let.group("ty"))
    return types


def infer_pointer_targets(types: Dict[str, TypeInfo]) -> Dict[str, str]:
    ptrs: Dict[str, str] = {}
    for name, info in types.items():
        if info.kind in {"ptr", "ref"} and info.element:
            ptrs[name] = info.element
    return ptrs


def split_blocks(lines: Sequence[str]) -> Dict[str, Block]:
    blocks: Dict[str, Block] = {}
    current_label: Optional[str] = None
    current_lines = []
    for raw in lines:
        m_start = re.match(r"^\s*(bb\d+):\s*\{", raw)
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


def strip_control_suffix(line: str) -> str:
    """Remove control flow suffixes like '-> [return: bbN]' from a statement line."""
    cleaned = line
    if "->" in cleaned:
        cleaned = cleaned.split("->", 1)[0]
    cleaned = cleaned.rstrip()
    if cleaned and not cleaned.endswith(";"):
        cleaned += ";"
    return cleaned

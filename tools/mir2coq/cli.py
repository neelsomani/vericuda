"""Command-line interface for mir2coq."""

from __future__ import annotations

import argparse
import pathlib
import sys

from .translator import MIRTranslator
from .render import coq_module, module_from_path, warning_log_path


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

    log_path = warning_log_path(args.output)
    if translator.warnings:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        header = [
            f"input: {args.input}",
            f"output: {args.output}",
            "warnings:",
        ]
        log_path.write_text("\n".join(header + translator.warnings) + "\n")
        print(f"[mir2coq] warnings logged to {log_path}")
    elif log_path.exists():
        log_path.unlink()

    print(f"[mir2coq] wrote {args.output} with {len(stmts)} statements")
    return 0

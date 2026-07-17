#!/usr/bin/env python3

import unittest

import mir2coq


class TranslatorHardeningTests(unittest.TestCase):
    def test_trailing_comment_cannot_create_barrier(self) -> None:
        lines = [
            "fn f(_1: *const u32) -> () {",
            "let _2: u32;",
            "_2 = copy (*_1); // scope 1 at source mentioning barrier()",
            "}",
        ]

        statements, _, _, diagnostics = mir2coq.parse_statements(lines)

        self.assertEqual(len(statements), 1)
        self.assertIsInstance(statements[0], mir2coq.LoadStmt)
        self.assertFalse(any(isinstance(s, mir2coq.BarrierStmt) for s in statements))
        self.assertEqual(diagnostics, [])

    def test_unknown_constant_is_rejected(self) -> None:
        with self.assertRaisesRegex(mir2coq.TranslationError, "unsupported MIR constant"):
            mir2coq.parse_operand("const mystery_payload")
        with self.assertRaisesRegex(mir2coq.TranslationError, "unsupported MIR constant"):
            mir2coq.parse_operand("const 1_u128")

    def test_unknown_type_is_rejected(self) -> None:
        with self.assertRaisesRegex(mir2coq.TranslationError, "unsupported MIR type"):
            mir2coq.classify_type("ImaginaryGpuWord")

    def test_unknown_pointer_element_type_is_rejected(self) -> None:
        with self.assertRaisesRegex(
            mir2coq.TranslationError, "unsupported pointer element type"
        ):
            mir2coq.classify_type("*mut u16")

    def test_missing_load_type_is_rejected(self) -> None:
        with self.assertRaisesRegex(
            mir2coq.TranslationError, "cannot determine supported MIR type"
        ):
            mir2coq.parse_statements(["_2 = copy (*_1);"])

    def test_loop_and_unhandled_terminators_are_loud(self) -> None:
        lines = [
            "fn f() -> () {",
            "bb1: {",
            "switchInt(copy _1) -> [0: bb2, otherwise: bb3];",
            "}",
            "bb3: {",
            "goto -> bb1;",
            "}",
        ]

        _, _, _, diagnostics = mir2coq.parse_statements(lines)

        self.assertTrue(any("switchInt terminator" in d for d in diagnostics))
        self.assertTrue(any("loop/back-edge bb3 -> bb1" in d for d in diagnostics))


if __name__ == "__main__":
    unittest.main()

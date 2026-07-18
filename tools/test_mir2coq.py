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

    def test_malformed_variable_operand_is_rejected(self) -> None:
        with self.assertRaisesRegex(mir2coq.TranslationError, "unsupported MIR operand"):
            mir2coq.parse_operand("_6)")
        with self.assertRaisesRegex(mir2coq.TranslationError, "unsupported MIR operand"):
            mir2coq.parse_operand("move _6)")

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

    def test_shared_param_routes_derived_loads_and_stores(self) -> None:
        lines = [
            "fn f(_1: *mut f32) -> () {",
            "let _2: *mut f32;",
            "let _3: f32;",
            "_2 = core::ptr::mut_ptr::<impl *mut f32>::add(copy _1, const 0_usize)",
            "_3 = copy (*_2);",
            "(*_2) = copy _3;",
            "}",
        ]

        statements, _, _, _ = mir2coq.parse_statements(
            lines, shared_params=["_1"]
        )

        self.assertEqual(len(statements), 2)
        self.assertIsInstance(statements[0], mir2coq.LoadStmt)
        self.assertTrue(statements[0].shared)
        self.assertIsInstance(statements[1], mir2coq.StoreStmt)
        self.assertTrue(statements[1].shared)
        self.assertIn("SLoadShared", statements[0].to_coq())
        self.assertIn("SStoreShared", statements[1].to_coq())

    def test_pointer_call_edges_do_not_leak_into_operands(self) -> None:
        lines = [
            "fn f(_1: *mut f32, _2: usize) -> () {",
            "let _3: *mut f32;",
            "let _4: f32;",
            "_3 = core::ptr::mut_ptr::<impl *mut f32>::add(copy _1, move _2) "
            "-> [return: bb1, unwind terminate(abi)];",
            "_4 = copy (*_3);",
            "}",
        ]

        statements, derived, _, _ = mir2coq.parse_statements(
            lines, shared_params=["_1"]
        )

        self.assertEqual(derived["_3"].to_coq(),
                         'M.EPtrAdd (M.EVar "_1") (M.EVar "_2")')
        self.assertEqual(len(statements), 1)
        self.assertNotIn('")"', statements[0].to_coq())

    def test_curated_fixed_loop_emits_sfor(self) -> None:
        lines = [
            "fn f() -> () {",
            "bb0: {",
            "_1 = model_barrier() -> [return: bb1, unwind terminate(abi)];",
            "}",
            "bb1: {",
            "_2 = core::ops::Range::<u32> { start: const 0_u32, end: const 3_u32 };",
            "switchInt(copy _3) -> [0: bb4, otherwise: bb2];",
            "}",
            "bb2: {",
            "_4 = model_barrier() -> [return: bb3, unwind terminate(abi)];",
            "}",
            "bb3: {",
            "goto -> bb1;",
            "}",
            "}",
        ]

        statements, _, _, diagnostics = mir2coq.parse_statements(lines)

        self.assertEqual(len(statements), 2)
        self.assertIsInstance(statements[0], mir2coq.BarrierStmt)
        self.assertIsInstance(statements[1], mir2coq.ForStmt)
        self.assertEqual(statements[1].bound, 3)
        self.assertFalse(any("loop/back-edge" in d for d in diagnostics))


if __name__ == "__main__":
    unittest.main()

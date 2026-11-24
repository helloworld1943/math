import unittest

from . import EncodingError, Program
from .conformance import (
    build_cases,
    lean_source,
    render_expression,
    verify_python,
)


class ConformanceTests(unittest.TestCase):
    def test_all_generated_cases_match_the_expected_decisions(self) -> None:
        p, cases = build_cases()
        self.assertEqual(len(cases), 111)
        self.assertEqual(len({case.name for case in cases}), len(cases))
        self.assertEqual(sum(case.accepted for case in cases), 48)
        verify_python(p, cases)

    def test_every_positive_and_negative_has_a_lean_assertion(self) -> None:
        p, cases = build_cases()
        source = lean_source(p.commit(), cases)
        self.assertEqual(source.count("-- "), len(cases))
        self.assertEqual(source.count("  fail_if_success"), 63)
        self.assertEqual(source.count("example :"), len(cases))
        self.assertNotIn("sorry", source)
        self.assertNotIn("axiom", source)

    def test_exporter_preserves_nested_binder_references(self) -> None:
        p = Program()
        a, x = p.variable(), p.variable()
        u0 = p.universe(0)
        expression = p.lambda_(a, u0, p.lambda_(x, p.type_node(a), a))
        self.assertEqual(
            render_expression(p.commit(), expression),
            "(fun (v0 : (Type 0)) => (fun (v1 : v0) => v0))",
        )

    def test_exporter_preserves_function_types_and_computed_arguments(self) -> None:
        p = Program()
        a, x = p.variable(), p.variable()
        u0 = p.universe(0)
        expression = p.function_type(
            a, u0, p.function_type(x, p.type_node(a), p.type_node(a))
        )
        snapshot = p.commit()
        self.assertEqual(
            render_expression(snapshot, expression),
            "((v0 : (Type 0)) → ((v1 : v0) → v0))",
        )
        identity = p.lambda_(a, p.universe(1), a)
        application = p.type_node(p.apply(identity, u0))
        self.assertEqual(
            render_expression(p.commit(), application),
            "((fun (v0 : (Type 1)) => v0) (Type 0))",
        )

    def test_exporter_rejects_open_variables_and_non_expressions(self) -> None:
        p = Program()
        variable = p.variable()
        relation = p.relation("HasType", p.universe(0), p.universe(1))
        snapshot = p.commit()
        with self.assertRaises(EncodingError):
            render_expression(snapshot, variable)
        with self.assertRaises(EncodingError):
            render_expression(snapshot, relation)


if __name__ == "__main__":
    unittest.main()

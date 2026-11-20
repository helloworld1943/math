import unittest

from layer0 import Node

from . import EncodingError, TypeCheckError
from . import _calculus as calculus
from .lean_examples import Example
from .logic_examples import LogicExamples


class LogicExampleTests(unittest.TestCase):
    def setUp(self) -> None:
        self.examples = LogicExamples()
        self.program = self.examples.program

    def require_type(self, example: Example) -> Node:
        relation = self.program.relation(
            "HasType", example.expression, example.type
        )
        self.program.commit().require(relation)
        return relation

    def assert_computes_to(self, expression: Node, expected: Node) -> None:
        snapshot = self.program.commit()
        reader = snapshot.view(expression, expected)._reader
        work = calculus.Work(100_000)
        actual = reader.term(expression, work)
        target = reader.term(expected, work)
        self.assertEqual(
            calculus.normalize(actual, work), calculus.normalize(target, work)
        )

    def test_fourteen_quantified_logic_examples_are_well_typed(self) -> None:
        examples = self.examples.logical()
        self.assertEqual(len(examples), 14)
        self.assertEqual(len({example.name for example in examples}), 14)
        for example in examples:
            with self.subTest(example=example.name):
                self.require_type(example)

    def test_forall_is_a_dependent_function_type_not_a_new_node(self) -> None:
        example = self.examples.forall_reorder()
        self.require_type(example)
        view = self.program.commit().view(example.type)
        self.assertEqual(view.kind(example.type), "TypeNode")
        self.assertEqual(view.form(example.type), "function")

    def test_exists_intro_followed_by_elimination_calls_handler_with_witness(self) -> None:
        e, p = self.examples, self.program
        intro, eliminate = e.exists_intro(), e.exists_elim()
        a, predicate, witness, proof, result, handler, i = e.variables(7)
        ta, tr = e.type_of(a), e.type_of(result)
        handler_type = p.function_type(
            i, ta, e.arrows(e.type_of(e.apply(predicate, i)), tr)
        )
        bindings = (
            (a, e.u0), (predicate, e.arrows(ta, e.u0)),
            (witness, ta), (proof, e.type_of(e.apply(predicate, witness))),
            (result, e.u0), (handler, handler_type),
        )
        package = e.apply(intro.expression, a, predicate, witness, proof)
        body = e.apply(eliminate.expression, a, predicate, package, result, handler)
        expression = e.lambdas(bindings, body)
        expected = e.lambdas(bindings, e.apply(handler, witness, proof))
        self.require_type(Example("existsRoundTrip", expression, e.forall(bindings, tr)))
        self.assert_computes_to(expression, expected)

    def test_encoded_exists_witness_extraction_returns_the_supplied_witness(self) -> None:
        e = self.examples
        intro, extract = e.exists_intro(), e.exists_witness()
        a, predicate, witness, proof = e.variables(4)
        ta = e.type_of(a)
        bindings = (
            (a, e.u0), (predicate, e.arrows(ta, e.u0)),
            (witness, ta), (proof, e.type_of(e.apply(predicate, witness))),
        )
        package = e.apply(intro.expression, a, predicate, witness, proof)
        expression = e.lambdas(
            bindings, e.apply(extract.expression, a, predicate, package)
        )
        expected = e.lambdas(bindings, witness)
        self.require_type(Example("extractWitness", expression, e.forall(bindings, ta)))
        self.assert_computes_to(expression, expected)

    def test_exists_map_changes_evidence_but_preserves_the_witness(self) -> None:
        e, p = self.examples, self.program
        intro, map_exists = e.exists_intro(), e.exists_map()
        a, pred_p, pred_q, transform, witness, proof, result, handler, i, j = (
            e.variables(10)
        )
        ta, tr = e.type_of(a), e.type_of(result)
        transform_type = p.function_type(
            i, ta, e.arrows(
                e.type_of(e.apply(pred_p, i)), e.type_of(e.apply(pred_q, i))
            ),
        )
        handler_type = p.function_type(
            j, ta, e.arrows(e.type_of(e.apply(pred_q, j)), tr)
        )
        bindings = (
            (a, e.u0), (pred_p, e.arrows(ta, e.u0)),
            (pred_q, e.arrows(ta, e.u0)), (transform, transform_type),
            (witness, ta), (proof, e.type_of(e.apply(pred_p, witness))),
            (result, e.u0), (handler, handler_type),
        )
        package = e.apply(intro.expression, a, pred_p, witness, proof)
        mapped = e.apply(map_exists.expression, a, pred_p, pred_q, transform, package)
        expression = e.lambdas(bindings, e.apply(mapped, result, handler))
        expected = e.lambdas(
            bindings, e.apply(handler, witness, e.apply(transform, witness, proof))
        )
        self.require_type(Example("mappedExists", expression, e.forall(bindings, tr)))
        self.assert_computes_to(expression, expected)

    def test_or_introductions_select_the_correct_handlers(self) -> None:
        e = self.examples
        eliminate = e.or_elim()
        for left in (True, False):
            with self.subTest(left=left):
                intro = e.or_intro(left)
                a, b, result, proof, on_left, on_right = e.variables(6)
                ta, tb, tr = e.type_of(a), e.type_of(b), e.type_of(result)
                bindings = (
                    (a, e.u0), (b, e.u0), (result, e.u0),
                    (proof, ta if left else tb),
                    (on_left, e.arrows(ta, tr)), (on_right, e.arrows(tb, tr)),
                )
                value = e.apply(intro.expression, a, b, proof)
                expression = e.lambdas(
                    bindings, e.apply(
                        eliminate.expression, a, b, result, value, on_left, on_right
                    ),
                )
                expected = e.lambdas(
                    bindings, e.apply(on_left if left else on_right, proof)
                )
                self.require_type(Example("orSelected", expression, e.forall(bindings, tr)))
                self.assert_computes_to(expression, expected)

    def test_equality_reflexivity_transport_returns_original_evidence(self) -> None:
        e = self.examples
        reflexivity, substitute = e.equality_refl(), e.equality_subst()
        a, x, predicate, proof = e.variables(4)
        ta = e.type_of(a)
        px = e.type_of(e.apply(predicate, x))
        bindings = (
            (a, e.u0), (x, ta),
            (predicate, e.arrows(ta, e.u0)), (proof, px),
        )
        equality = e.apply(reflexivity.expression, a, x)
        expression = e.lambdas(
            bindings, e.apply(substitute.expression, a, x, x, equality, predicate, proof)
        )
        expected = e.lambdas(bindings, proof)
        self.require_type(Example("transportRefl", expression, e.forall(bindings, px)))
        self.assert_computes_to(expression, expected)

    def test_equality_symmetry_of_reflexivity_computes_to_reflexivity(self) -> None:
        e = self.examples
        refl, symmetry = e.equality_refl(), e.equality_symm()
        a, x = e.variables(2)
        ta = e.type_of(a)
        bindings = ((a, e.u0), (x, ta))
        evidence = e.apply(refl.expression, a, x)
        expression = e.lambdas(
            bindings, e.apply(symmetry.expression, a, x, x, evidence)
        )
        expected = e.lambdas(bindings, evidence)
        self.require_type(Example(
            "symmetricRefl", expression, e.forall(bindings, e.equality_type(ta, x, x))
        ))
        self.assert_computes_to(expression, expected)

    def test_equality_transitivity_of_reflexivity_computes_to_reflexivity(self) -> None:
        e = self.examples
        refl, transitivity = e.equality_refl(), e.equality_trans()
        a, x = e.variables(2)
        ta = e.type_of(a)
        bindings = ((a, e.u0), (x, ta))
        evidence = e.apply(refl.expression, a, x)
        expression = e.lambdas(
            bindings, e.apply(transitivity.expression, a, x, x, x, evidence, evidence)
        )
        expected = e.lambdas(bindings, evidence)
        self.require_type(Example(
            "transitiveRefl", expression, e.forall(bindings, e.equality_type(ta, x, x))
        ))
        self.assert_computes_to(expression, expected)

    def test_exists_intro_rejects_evidence_for_a_different_witness(self) -> None:
        e = self.examples
        intro = e.exists_intro()
        a, predicate, x, y, proof = e.variables(5)
        ta = e.type_of(a)
        bindings = (
            (a, e.u0), (predicate, e.arrows(ta, e.u0)),
            (x, ta), (y, ta), (proof, e.type_of(e.apply(predicate, x))),
        )
        expression = e.lambdas(
            bindings, e.apply(intro.expression, a, predicate, y, proof)
        )
        with self.assertRaisesRegex(TypeCheckError, "argument type"):
            self.require_type(Example(
                "wrongExistsEvidence", expression,
                e.forall(bindings, e.exists_type(ta, predicate)),
            ))

    def test_forall_result_cannot_be_used_at_a_different_index(self) -> None:
        e, p = self.examples, self.program
        a, predicate, f, x, y, i = e.variables(6)
        ta = e.type_of(a)
        f_type = p.function_type(i, ta, e.type_of(e.apply(predicate, i)))
        bindings = (
            (a, e.u0), (predicate, e.arrows(ta, e.u0)),
            (f, f_type), (x, ta), (y, ta),
        )
        expression = e.lambdas(bindings, e.apply(f, x))
        with self.assertRaises(TypeCheckError):
            self.require_type(Example(
                "wrongForallIndex", expression,
                e.forall(bindings, e.type_of(e.apply(predicate, y))),
            ))

    def test_wrong_or_branch_evidence_is_rejected(self) -> None:
        e = self.examples
        intro = e.or_intro(True)
        a, b, proof = e.variables(3)
        ta, tb = e.type_of(a), e.type_of(b)
        bindings = ((a, e.u0), (b, e.u0), (proof, tb))
        expression = e.lambdas(bindings, e.apply(intro.expression, a, b, proof))
        with self.assertRaisesRegex(TypeCheckError, "argument type"):
            self.require_type(Example(
                "wrongOrEvidence", expression, e.forall(bindings, e.or_type(ta, tb))
            ))

    def test_encoded_exists_cannot_eliminate_at_an_unavailable_universe_level(self) -> None:
        e = self.examples
        a, predicate, package, x, proof = e.variables(5)
        ta = e.type_of(a)
        bindings = (
            (a, e.u0), (predicate, e.arrows(ta, e.u0)),
            (package, e.exists_type(ta, predicate)),
        )
        handler = e.lambdas(
            ((x, ta), (proof, e.type_of(e.apply(predicate, x)))), a
        )
        expression = e.lambdas(bindings, e.apply(package, e.u0, handler))
        with self.assertRaisesRegex(TypeCheckError, "argument type"):
            self.require_type(Example(
                "tooLargeElimination", expression, e.forall(bindings, e.u0)
            ))

    def test_quantifying_over_small_types_raises_the_result_universe(self) -> None:
        e, p = self.examples, self.program
        small = e.empty_type()
        self.require_type(Example("smallForall", small, e.u1))
        with self.assertRaises(TypeCheckError):
            self.require_type(Example("notImpredicative", small, e.u0))
        a = p.variable()
        high = p.function_type(
            a, e.u1, e.arrows(e.type_of(a), e.type_of(a))
        )
        self.require_type(Example("highForall", high, p.universe(2)))
        with self.assertRaises(TypeCheckError):
            self.require_type(Example("notProp", high, e.u0))

    def test_encoded_exists_disjunction_and_equality_live_in_u1(self) -> None:
        e = self.examples
        a, predicate, x, y, q = e.variables(5)
        ta = e.type_of(a)
        descriptions = (
            (
                ((a, e.u0), (predicate, e.arrows(ta, e.u0))),
                e.exists_type(ta, predicate),
            ),
            (((a, e.u0), (q, e.u0)), e.or_type(ta, e.type_of(q))),
            (((a, e.u0), (x, ta), (y, ta)), e.equality_type(ta, x, y)),
        )
        for bindings, description in descriptions:
            with self.subTest(description=description.number):
                expression = e.lambdas(bindings, description)
                self.require_type(Example(
                    "encodedUniverse", expression, e.forall(bindings, e.u1)
                ))
                with self.assertRaises(TypeCheckError):
                    self.require_type(Example(
                        "wrongEncodedUniverse", expression, e.forall(bindings, e.u0)
                    ))

    def test_u0_inhabitants_are_not_automatically_proof_irrelevant(self) -> None:
        with self.assertRaisesRegex(TypeCheckError, "supplied type"):
            self.require_type(self.examples.proof_identity_sensitive())

    def test_an_arbitrary_type_variable_is_not_a_primitive_universe(self) -> None:
        e = self.examples
        sort_like, a, x = e.variables(3)
        bindings = (
            (sort_like, e.u1), (a, e.type_of(sort_like)), (x, e.type_of(a)),
        )
        expression = e.lambdas(bindings, x)
        supplied = e.forall(bindings, e.type_of(a))
        with self.assertRaisesRegex(TypeCheckError, "Universe type"):
            self.require_type(Example("notEveryTypeIsASort", expression, supplied))

    def test_universe_nodes_are_constants_not_variable_declarations(self) -> None:
        p = self.program
        snapshot = p.commit()
        self.assertEqual(snapshot.view(self.examples.u0).kind(self.examples.u0), "Universe")
        self.assertEqual(snapshot.view(self.examples.u0).level(self.examples.u0), 0)
        with self.assertRaisesRegex(EncodingError, "Variable"):
            p.lambda_(self.examples.u0, self.examples.u1, self.examples.u0)

    def test_uninhabited_statement_is_not_proved_by_returning_its_type(self) -> None:
        e, p = self.examples, self.program
        a = p.variable()
        invalid = p.lambda_(a, e.u0, a)
        with self.assertRaises(TypeCheckError):
            self.require_type(Example("inventedProof", invalid, e.empty_type()))

    def test_quantified_encodings_are_not_validator_relation_or_groups(self) -> None:
        e, p = self.examples, self.program
        intro = e.or_intro(True)
        evidence_type = p.relation("HasType", intro.expression, intro.type)
        invalid_claim = p.relation("HasType", intro.expression, e.u0)
        validation = p.any_of(
            intro.expression, intro.type, e.u0,
            relations=(invalid_claim, evidence_type),
        )
        snapshot = p.commit()
        snapshot.require(validation)
        self.assertEqual(snapshot.view(intro.expression).kind(intro.expression), "Lambda")
        self.assertEqual(snapshot.view(validation).kind(validation), "Relation")
        with self.assertRaises(EncodingError):
            p.any_of(intro.expression, intro.type, relations=(intro.expression,))
        with self.assertRaises(EncodingError):
            p.relation("Exists", intro.expression, intro.type)


if __name__ == "__main__":
    unittest.main()

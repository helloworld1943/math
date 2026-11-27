import unittest

from .language import LanguageError, parse, run_source
from .runtime import World


SCHEMA = """
public class Functions{}

class Truth:Prop {}
constructor func Truth.intro() Truth {}
class Impossible:Prop {}
class Any:Sort(2) {
    const A:Type;
    TypeDef B:A->Prop;const b:B;
}
constructor func Any.intro(A a,B b) Prop {
    this.A=a;
    this.b=b;
}
static func Functions.always(Nat n) Prop { return Truth; }
static func Functions.never(Nat n) Prop { return Impossible; }
"""

EVIDENCE = """
const Prop P=Any.intro(Nat,Functions.always);
class Evidence:P {
    TypeDef H:((x:P.A)->P.b(x));const h:H;
}
constructor func Evidence.intro(h) Evidence { this.h=h; }
static func Functions.proof(Nat n) Truth { return Truth.intro(); }
"""

QUANTIFIERS = """
public class Functions{}

class Truth:Prop{}
constructor func Truth() Truth {}
class Another:Prop{}
constructor func Another() Another {}
class Falsehood:Prop{}
class Any:Sort(2){const A:Type;TypeDef B:A->Prop;const b:B;}
constructor func Any(A a,B b) Prop{this.A=a;this.b=b;}
class Exists:Sort(2){const A:Type;TypeDef B:A->Prop;const b:B;}
constructor func Exists(A a,B b) Prop{this.A=a;this.b=b;}
static func Functions.always(Nat n) Prop{return Truth;}
static func Functions.never(Nat n) Prop{return Falsehood;}
static func Functions.proof(Nat n) Truth{return Truth();}
static func Functions.boolProof(Bool b) Truth{return Truth();}
"""

UNIVERSAL = """
const Prop All=Any(Nat,Functions.always);
class AllEvidence:All{TypeDef H:((x:All.A)->All.b(x));const h:H;}
constructor func AllEvidence(H h) AllEvidence {this.h=h;}
static func H AllEvidence.prove{return Truth();}
"""

EXISTENTIAL = """
const Prop Some=Exists(Nat,Functions.always);
class SomeEvidence:Some{const witness:Some.A;TypeDef H:Some.b(witness);const h:H;}
constructor func SomeEvidence(Some.A witness,H h) Some {this.witness=witness;this.h=h;}
"""


class GeneratedPropositionTests(unittest.TestCase):
    def reject(self, source, message=None, packages=None):
        with self.assertRaises(LanguageError) as caught:
            run_source(source, packages)
        self.assertEqual(caught.exception.stage, "type")
        if message:
            self.assertIn(message, caught.exception.message)
        return caught.exception

    def test_explicit_generator_and_object_constructor_have_different_results(self):
        source = SCHEMA + """
            class Pair { const Int a; const Int b; }
            constructor func Pair.make(a,b) Pair { this.a=a;this.b=b; }
            Pair object=Pair.make(1,2);
            const Prop P=Any.intro(Nat,Functions.always);
            print(P);print(object.a);
        """
        result = run_source(source)
        generator = next(fn for fn in result["functions"] if fn["name"] == "Any.intro")
        ordinary = next(fn for fn in result["functions"] if fn["name"] == "Pair.make")
        self.assertTrue(generator["generator"])
        self.assertEqual(generator["returns"], "Sort(0)")
        self.assertFalse(ordinary["generator"])
        self.assertEqual(ordinary["returns"], "Pair")
        self.assertEqual(result["output"], ["Any(A=Nat, b=always)", "1"])
        self.assertNotIn("Any", [obj["type"] for obj in result["objects"]])

    def test_constructor_result_annotations_accept_own_targets_and_numeric_prop(self):
        result = run_source("""
            class Truth:Prop{}constructor func Truth() Truth {}
            class Functions{}
            static func Functions.always(Nat n) Prop{return Truth;}
            class Any:Sort(2){const A:Type;TypeDef B:A->Prop;const b:B;}
            constructor func Any.intro(A a,B b) Sort(0){this.A=a;this.b=b;}
            class Cell{Int value;}
            constructor func Cell(value) Cell{this.value=value;}
            const Prop P=Any.intro(Nat,Functions.always);
            Cell c=Cell(4);
            print(P.b(Nat(1)));print(c.value);
        """)
        self.assertEqual(result["output"], ["Truth", "4"])
        program = parse("""
            class Truth:Prop{}constructor func Truth() Truth{}
            class Cell{Int value;}constructor func Cell(value) Cell{this.value=value;}
        """)
        constructors = [node for node in program.items() if program.description(node).kind == "constructor"]
        self.assertTrue(all(len(program.description(node).children) == 4 for node in constructors))
        self.assertTrue(all(program.description(program.description(node).children[2]).kind == "named_type"
                            for node in constructors))
        self.assertFalse(any(node["kind"] in {"constructor_result", "constructor_name", "constructor_owner", "procedure"}
                             for node in result["nodes"]))
        self.assertTrue(any(node["kind"] == "sort_type" for node in result["nodes"]))
        self.assertTrue(any(node["kind"] == "named_type" for node in result["nodes"]))

    def test_evidence_result_accepts_explicit_generated_target_or_builder_alias(self):
        for result_type in ("P", "Evidence"):
            with self.subTest(result_type=result_type):
                source = SCHEMA + EVIDENCE.replace("intro(h) Evidence", f"intro(h) {result_type}")
                result = run_source(source + "P h=Evidence.intro(Functions.proof);print(h);")
                self.assertEqual(result["output"], ["<proof Any(A=Nat, b=always)>"])
                constructor = next(fn for fn in result["functions"] if fn["name"] == "Evidence.intro")
                self.assertEqual(constructor["returns"], "Any(A=Nat, b=always)")
        self.reject(SCHEMA + EVIDENCE.replace("intro(h) Evidence", "intro(h) Any"), "constructor result")
        self.reject(SCHEMA + EVIDENCE.replace("intro(h) Evidence", "intro(h) Prop"), "data specification")

    def test_schema_proposition_and_proof_are_three_distinct_typing_roles(self):
        source = SCHEMA + EVIDENCE + "P h=Evidence.intro(Functions.proof);print(h);"
        result = run_source(source)
        schema = next(class_spec for class_spec in result["classes"] if class_spec["name"] == "Any")
        builder = next(class_spec for class_spec in result["classes"] if class_spec["name"] == "Evidence")
        self.assertEqual(schema["sort"], 2)
        self.assertIsNone(schema["evidenceTarget"])
        self.assertEqual(builder["evidenceTarget"], "Any(A=Nat, b=always)")
        self.assertEqual(result["variables"]["P"], {"typeValue": "Any(A=Nat, b=always)"})
        self.assertEqual(result["objects"][0]["type"], "Any(A=Nat, b=always)")
        self.assertTrue(result["objects"][0]["prop"])
        self.assertEqual(result["objects"][0]["fields"], {})
        self.assertEqual(result["output"], ["<proof Any(A=Nat, b=always)>"])
        self.reject(SCHEMA + "Any object=Any.intro(Nat,Functions.always);", "Expected Any")
        self.reject(SCHEMA + EVIDENCE + "Prop h=Evidence.intro(Functions.proof);", "Expected Sort(0)")

    def test_generator_constructs_a_statement_even_when_no_evidence_exists(self):
        result = run_source(SCHEMA + "const Prop P=Any.intro(Nat,Functions.never);print(P);")
        self.assertEqual(result["output"], ["Any(A=Nat, b=never)"])
        self.assertEqual(result["objects"], [])
        self.assertEqual(len(result["generatedPropositions"]), 1)
        self.assertEqual(result["generatedPropositions"][0]["evidenceSpecifications"], [])

    def test_unnamed_generators_and_evidence_constructors_keep_their_distinct_results(self):
        result = run_source(QUANTIFIERS + UNIVERSAL + EXISTENTIAL + """
            All universal=AllEvidence(AllEvidence.prove);
            Some existential=SomeEvidence(Nat(3),Truth());
            print(universal);print(existential);
        """)
        self.assertEqual(result["output"], [
            "<proof Any(A=Nat, b=always)>", "<proof Exists(A=Nat, b=always)>",
        ])
        generators = [fn for fn in result["functions"] if fn["generator"]]
        self.assertEqual({fn["name"] for fn in generators}, {"Any", "Exists"})
        self.assertTrue(all(fn["unnamed"] and fn["returns"] == "Sort(0)" for fn in generators))
        evidence = next(fn for fn in result["functions"] if fn["name"] == "SomeEvidence")
        self.assertEqual(evidence["returns"], "Exists(A=Nat, b=always)")
        self.assertEqual(evidence["parameters"], [("witness", "Nat"), ("h", "Truth")])

    def test_unnamed_generator_and_named_alternative_have_equal_information(self):
        result = run_source(QUANTIFIERS + UNIVERSAL + """
            constructor func Any.alternative(A a,B b) Prop{this.A=a;this.b=b;}
            const Prop Other=Any.alternative(Nat,Functions.always);
            All h=AllEvidence(AllEvidence.prove);
            Other same=h;print(All==Other);
        """)
        self.assertEqual(result["output"], ["true"])
        self.assertEqual(len(result["generatedPropositions"]), 1)

    def test_universal_introduction_requires_a_function_not_one_proof(self):
        self.reject(QUANTIFIERS + UNIVERSAL + "All wrong=AllEvidence(Truth());", "Expected")
        self.reject(QUANTIFIERS + UNIVERSAL + "All wrong=AllEvidence(Functions.boolProof);", "Expected")

    def test_existential_introduction_requires_both_witness_and_matching_proof(self):
        for arguments in ("", "Nat(3)", "true,Truth()", "Nat(3),Another()", "Nat(3),Functions.proof"):
            with self.subTest(arguments=arguments):
                self.reject(QUANTIFIERS + EXISTENTIAL + f"Some wrong=SomeEvidence({arguments});")

    def test_quantifiers_can_be_formed_for_an_uninhabited_predicate(self):
        result = run_source(QUANTIFIERS + """
            const Prop AllFalse=Any(Nat,Functions.never);
            const Prop SomeFalse=Exists(Nat,Functions.never);
            print(AllFalse);print(SomeFalse);
        """)
        self.assertEqual(result["output"], ["Any(A=Nat, b=never)", "Exists(A=Nat, b=never)"])
        self.assertEqual(result["objects"], [])
        self.assertTrue(all(not p["evidenceSpecifications"] for p in result["generatedPropositions"]))
        self.reject(QUANTIFIERS + UNIVERSAL.replace("Functions.always", "Functions.never") +
                    "All wrong=AllEvidence(AllEvidence.prove);", "Expected")
        self.reject(QUANTIFIERS + EXISTENTIAL.replace("Functions.always", "Functions.never") +
                    "Some wrong=SomeEvidence(Nat(3),Truth());", "Expected")

    def test_any_and_exists_are_different_propositions_even_with_identical_metadata(self):
        self.reject(QUANTIFIERS + UNIVERSAL + EXISTENTIAL +
                    "Some e=SomeEvidence(Nat(3),Truth());All wrong=e;", "Expected")
        self.assertEqual(run_source(QUANTIFIERS + UNIVERSAL + EXISTENTIAL + "print(All==Some);")["output"], ["false"])

    def test_existential_witnesses_do_not_change_the_target_proposition(self):
        result = run_source(QUANTIFIERS + EXISTENTIAL + """
            Some first=SomeEvidence(Nat(3),Truth());
            Some second=SomeEvidence(Nat(4),Truth());
            print(first==second);print(first);print(second);
        """)
        self.assertEqual(result["output"], [
            "false", "<proof Exists(A=Nat, b=always)>", "<proof Exists(A=Nat, b=always)>",
        ])
        self.assertEqual({obj["type"] for obj in result["objects"]}, {"Exists(A=Nat, b=always)"})

    def test_quantifier_predicates_can_depend_on_the_actual_class_argument(self):
        source = QUANTIFIERS + """
            class Packed{const p:Prop;const h:p;}
            constructor func Packed(p,h) Packed {this.p=p;this.h=h;}
            static func Functions.project(Packed x) Prop{return x.p;}
            const Prop All=Any(Packed,Functions.project);
            class AllEvidence:All{TypeDef H:((x:All.A)->All.b(x));const h:H;}
            constructor func AllEvidence(H h) AllEvidence {this.h=h;}
static func H AllEvidence.prove{return x.h;}
            static func Functions.constantProof(Packed x) Truth{return Truth();}
            const Prop Some=Exists(Packed,Functions.project);
            class SomeEvidence:Some{const witness:Some.A;TypeDef H:Some.b(witness);const h:H;}
            constructor func SomeEvidence(Some.A witness,H h) Some{this.witness=witness;this.h=h;return this;}
            const Packed first=Packed(Truth,Truth());
            const Packed second=Packed(Another,Another());
        """
        result = run_source(source + """
            All universal=AllEvidence(AllEvidence.prove);
            Some a=SomeEvidence(first,Truth());
            Some b=SomeEvidence(second,Another());
            print(All.b(first));print(All.b(second));
            print(Some.b(first));print(Some.b(second));
            print(universal);print(a);print(b);
        """)
        self.assertEqual(result["output"], [
            "Truth", "Another", "Truth", "Another", "<proof Any(A=Packed, b=project)>",
            "<proof Exists(A=Packed, b=project)>", "<proof Exists(A=Packed, b=project)>",
        ])
        self.reject(source + "Some wrong=SomeEvidence(second,Truth());", "Expected")
        colon = source.replace("Some.A witness", "witness:Some.A")
        self.assertEqual(run_source(colon + "Some h=SomeEvidence(second,Another());print(h);")["output"],
                         ["<proof Exists(A=Packed, b=project)>"])
        self.reject(colon + "Some wrong=SomeEvidence(second,Truth());", "Expected")
        self.reject(source.replace("Some.A witness,H h", "H h,Some.A witness"), "dependency order")
        self.reject(source + "All wrong=AllEvidence(Functions.constantProof);", "Expected")
        self.reject(source + "Packed wrong=Packed(Another,Truth());", "Expected")

    def test_unnamed_quantifier_constructors_cannot_bypass_totality_or_proof_opacity(self):
        self.reject(QUANTIFIERS + UNIVERSAL +
                    "static func Functions.loop(Nat n) Truth{return Functions.loop(n);}All wrong=AllEvidence(Functions.loop);", "Recursive")
        self.reject(QUANTIFIERS + UNIVERSAL +
                    "All h=AllEvidence(AllEvidence.prove);print(h.h);", "Unknown field")
        self.reject(QUANTIFIERS + EXISTENTIAL +
                    "Some h=SomeEvidence(Nat(3),Truth());print(h.witness);", "Unknown field")
        for suffix in ("Some h;", "Some h=nil;", "Some h=SomeEvidence{};"):
            self.reject(QUANTIFIERS + EXISTENTIAL + suffix)

    def test_evidence_constructor_uses_the_particular_target_not_a_new_class_type(self):
        result = run_source(SCHEMA + EVIDENCE + """
            P h=Evidence.intro(Functions.proof);
            Evidence also=Evidence.intro(Functions.proof);
            print(h);print(also);
        """)
        constructor = next(fn for fn in result["functions"] if fn["name"] == "Evidence.intro")
        self.assertEqual(constructor["returns"], "Any(A=Nat, b=always)")
        self.assertEqual(constructor["parameters"], [("h", "((x:Nat) -> Truth)")])
        self.assertEqual({obj["type"] for obj in result["objects"]}, {"Any(A=Nat, b=always)"})

    def test_metadata_is_readable_on_the_proposition_not_on_its_proof(self):
        result = run_source(SCHEMA + EVIDENCE + """
            print(P.A);print(P.b(Nat(3)));
            P h=Evidence.intro(Functions.proof);
        """)
        self.assertEqual(result["output"], ["Nat", "Truth"])
        self.reject(SCHEMA + EVIDENCE + "P h=Evidence.intro(Functions.proof);print(h.A);", "Unknown field")
        self.reject(SCHEMA + EVIDENCE + "P h=Evidence.intro(Functions.proof);print(h.h);", "Unknown field")

    def test_evidence_is_checked_against_the_generated_predicate(self):
        self.reject(SCHEMA + EVIDENCE + "static func Functions.wrong(Nat n) Bool{return true;}P h=Evidence.intro(Functions.wrong);", "Expected")
        self.reject(SCHEMA + """
            const Prop P=Any.intro(Nat,Functions.never);
            class Evidence:P { TypeDef H:((x:P.A)->P.b(x));const h:H; }
            constructor func Evidence.intro(h) Evidence {this.h=h;}
            static func Functions.wrong(Nat n) Truth{return Truth.intro();}
            P h=Evidence.intro(Functions.wrong);
        """, "Expected")

    def test_different_domains_or_predicates_produce_different_target_types(self):
        self.reject(SCHEMA + EVIDENCE + """
            const Prop Other=Any.intro(Nat,Functions.never);
            P h=Evidence.intro(Functions.proof);
            Other wrong=h;
        """, "Expected")
        result = run_source(SCHEMA + """
            static func Functions.onBool(Bool b) Prop{return Truth;}
            const Prop Natural=Any.intro(Nat,Functions.always);
            const Prop Boolean=Any.intro(Bool,Functions.onBool);
            print(Natural==Boolean);
        """)
        self.assertEqual(result["output"], ["false"])

    def test_equal_information_from_different_constructors_is_semantically_equal(self):
        result = run_source(SCHEMA + EVIDENCE + """
            constructor func Any.alternative(A a,B b) Prop {this.A=a;this.b=b;}
            const Prop Again=Any.alternative(Nat,Functions.always);
            P h=Evidence.intro(Functions.proof);
            Again reused=h;
            print(P==Again);
        """)
        self.assertEqual(result["output"], ["true"])
        self.assertEqual(len(result["generatedPropositions"]), 1)
        program = parse("Int x=1;Int y=1;")
        literals = [node for node, info in program.descriptions.items() if info.kind == "integer"]
        self.assertIsNot(literals[0], literals[1])

    def test_alpha_equivalent_predicates_do_not_require_node_identity(self):
        result = run_source(SCHEMA + """
            static func Functions.renamed(Nat k) Prop{return Truth;}
            const Prop P=Any.intro(Nat,Functions.always);
            const Prop Q=Any.intro(Nat,Functions.renamed);
            class Evidence:P { TypeDef H:((x:P.A)->P.b(x));const h:H; }
            constructor func Evidence.intro(h) Evidence {this.h=h;}
            static func Functions.proof(Nat k) Truth{return Truth.intro();}
            P h=Evidence.intro(Functions.proof);Q same=h;print(P==Q);
        """)
        self.assertEqual(result["output"], ["true"])

    def test_multiple_evidence_constructors_target_the_same_proposition(self):
        result = run_source(SCHEMA + EVIDENCE + """
            constructor func Evidence.other(h) Evidence {this.h=h;return this;}
            P a=Evidence.intro(Functions.proof);P b=Evidence.other(Functions.proof);
            print(a==b);
        """)
        self.assertEqual(result["output"], ["false"])
        self.assertEqual({obj["type"] for obj in result["objects"]}, {"Any(A=Nat, b=always)"})
        result = run_source(SCHEMA + EVIDENCE + """
            constructor func Evidence.explicit(h) P{this.h=h;return this;}
            static func Functions.introduced() P {return Evidence.explicit(Functions.proof);}
            P h=Evidence.explicit(Functions.proof);print(h);
            P another=Functions.introduced();print(another);
        """)
        self.assertEqual(result["output"], ["<proof Any(A=Nat, b=always)>"] * 2)

    def test_generator_input_names_infer_schema_field_types_and_order(self):
        world = World(parse(SCHEMA), {})
        world.check()
        generator = next(fn for fn in world.functions if fn.name == "intro" and fn.constructor.name == "Any")
        self.assertEqual([str(kind) for _, kind, _ in generator.parameters], ["Sort(1)", "(a -> Sort(0))"])
        self.assertTrue(generator.schema_parameters)
        self.reject("""
            class Any:Sort(2){const A:Type;TypeDef B:A->Prop;const b:B;}
            constructor func Any.intro(B b,A a) Prop {this.A=a;this.b=b;}
        """, "dependency order")

    def test_ordinary_func_interfaces_are_still_non_dependent(self):
        self.reject("\npublic class Functions{}\nstatic func Functions.id(A:Type,x:A) A{return x;}", "non-dependent")
        self.reject(SCHEMA + "constructor func Any.wrong(A:Type,B:A->Prop) Prop {this.A=a;this.b=b;}", "simple names")

    def test_bad_generator_input_values_and_missing_fields(self):
        self.reject(SCHEMA + "const Prop P=Any.intro(3,Functions.always);", "Sort")
        self.reject(SCHEMA + "const Prop P=Any.intro(Bool,Functions.always);", "Expected")
        self.reject("""
            class Any:Sort(2){const A:Type;TypeDef B:A->Prop;const b:B;}
            constructor func Any.intro(A a,B b) Prop {this.A=a;}
        """, "uninitialized")
        self.reject("""
            class Any:Sort(2){const A:Type;TypeDef B:A->Prop;const b:B;}
            constructor func Any.intro(A a,B b) Prop {this.b=b;this.A=a;}
        """, "before")

    def test_generator_fields_and_inputs_must_be_stable(self):
        self.reject("""
            class Any:Sort(2){A:Type;}
            constructor func Any.intro(A) Prop {this.A=a;}
        """, "must be const")
        self.reject(SCHEMA + "Type A=Nat;const Prop P=Any.intro(A,Functions.always);", "must be const")
        self.reject(SCHEMA + "Nat->Prop B=Functions.always;const Prop P=Any.intro(Nat,B);", "must be const")
        result = run_source(SCHEMA + "const Type A=Nat;const Nat->Prop B=Functions.always;const Prop P=Any.intro(A,B);print(P.A);")
        self.assertEqual(result["output"], ["Nat"])
        self.reject(SCHEMA + "const Prop P=Any.intro(Nat,Functions.always);P.A=Bool;", "immutable")
        self.reject(SCHEMA + EVIDENCE + "const Prop P2=Any.intro(Nat,Functions.always);P=P2;", "const")

    def test_generator_body_is_metadata_construction_not_arbitrary_effects(self):
        for suffix in ("print(1);", "while(true){}", "Int local=1;"):
            self.reject("""
                class S{const Int n;}
                constructor func S.make(n) Prop {this.n=n;
            """ + suffix + "}", "generator only initializes")
        self.reject("class S{const Int n;}constructor func S.make(n) Prop {return this;}", "initialized")
        self.reject("class S{const Int n;}constructor func S.make(n) Prop {this.n=n;return S{n:n};}", "own this")

    def test_instance_or_proof_schemas_cannot_be_used_as_prop_generators(self):
        self.reject("class P:Prop{}constructor func P.make() Prop{}", "data specification")
        self.reject(SCHEMA + EVIDENCE + "constructor func Evidence.generate(h) Prop{this.h=h;}", "data specification")

    def test_explicit_result_annotation_is_not_an_arbitrary_cast(self):
        self.reject("class X{}constructor func X.make() Int{}", "result must")
        self.reject("class X{}constructor func X.make() Type{}", "result must")
        self.reject("class X{}constructor func X.make() Prop{return Nat;}", "own this")

    def test_nil_defaults_and_literals_cannot_create_generated_proofs(self):
        for suffix in ("P h;", "P h=nil;", "P h=P(nil);", "P h=P{};",
                       "Evidence h;", "Evidence h=nil;", "Evidence h=Evidence{};"):
            with self.subTest(suffix=suffix):
                self.reject(SCHEMA + EVIDENCE + suffix)

    def test_evidence_constructor_completeness_and_const_fields(self):
        prefix = SCHEMA + "const Prop P=Any.intro(Nat,Functions.always);class Evidence:P{TypeDef H:((x:P.A)->P.b(x));const h:H;}"
        self.reject(prefix + "constructor func Evidence.intro() Evidence {}", "uninitialized")
        self.reject(prefix + "constructor func Evidence.intro(h) Evidence {this.h=h;this.h=h;}", "already initialized")
        self.reject(prefix + "constructor func Evidence.intro(h) Evidence {Evidence copy=this;this.h=h;}", "cannot escape")
        self.reject(prefix + "constructor func Evidence.intro(h) Evidence {this.h=h;Evidence copy=this;}", "schema object cannot escape")

    def test_target_must_be_a_particular_immutable_generated_proposition(self):
        self.reject(SCHEMA + "Prop P=Any.intro(Nat,Functions.always);class E:P{}", "must be const")
        self.reject(SCHEMA + "Any spec;class E:spec{}", "must be const")
        self.reject(SCHEMA + "class E:Any{}", "particular generated")
        self.reject("class E:Nat{}", "sort must")
        self.reject(SCHEMA + "class E:Any.inhabitant{}", "unknown")
        self.reject(SCHEMA + "const Prop P=Truth;class E:P{}", "generated proposition")

    def test_recursive_evidence_rules_do_not_bypass_positivity(self):
        self.reject(SCHEMA + "const Prop P=Any.intro(Nat,Functions.always);class E:P{const h:P;}", "positivity")
        self.reject(SCHEMA + "const Prop P=Any.intro(Nat,Functions.always);class E:P{const h:P->Truth;}", "positivity")

    def test_nonterminating_evidence_and_nil_are_not_proofs(self):
        self.reject(SCHEMA + EVIDENCE + "static func Functions.loop(Nat n) Truth{return Functions.loop(n);}P h=Evidence.intro(Functions.loop);", "Recursive code")
        self.reject(SCHEMA + EVIDENCE + "P h=Evidence.intro(nil);", "class type")

    def test_universe_bound_applies_to_the_specification(self):
        self.reject("""
            class Any:Type{const A:Type;TypeDef B:A->Prop;const b:B;}
            constructor func Any.intro(A a,B b) Prop {this.A=a;this.b=b;}
        """, "above class")
        self.reject(SCHEMA + "const Prop P=Any.intro(Type,Functions.always);", "Expected Sort(1)")

    def test_parameter_substitution_keeps_nominal_proposition_information(self):
        result = run_source(SCHEMA + EVIDENCE + """
            P h=Evidence.intro(Functions.proof);
            static func Functions.use(P h) P{return h;}
            print(Functions.use(h));
        """)
        self.assertEqual(result["output"], ["<proof Any(A=Nat, b=always)>"])

    def test_annotations_and_generators_are_separate_from_node_values(self):
        result = run_source(SCHEMA + EVIDENCE + "P h=Evidence.intro(Functions.proof);")
        constructor_nodes = [node for node in result["nodes"] if node.get("constructor") is True]
        self.assertEqual(len(constructor_nodes), 3)
        self.assertEqual(sum(node.get("generator") is True for node in result["nodes"]), 1)
        self.assertTrue(all(node["value"] is None for node in constructor_nodes))
        any_node = next(node for node in result["nodes"] if node.get("sort") == 2 and node["kind"] == "class_decl")
        self.assertEqual(any_node["type"], "Sort(2)")

    def test_generated_metadata_is_not_tied_to_the_generator_function_name(self):
        result = run_source("""
            class Tagged{const Int kind;}
            constructor func Tagged.first(kind) Prop{this.kind=kind;}
            constructor func Tagged.second(kind) Prop{this.kind=kind;}
            const Prop A=Tagged.first(1);
            const Prop B=Tagged.second(1);
            const Prop C=Tagged.first(2);
            print(A==B);print(A==C);print(C.kind);
        """)
        self.assertEqual(result["output"], ["true", "false", "2"])

    def test_generated_type_has_no_automatic_evidence_even_with_empty_schema(self):
        result = run_source("""
            class Specification{}
            constructor func Specification.statement() Prop{}
            const Prop P=Specification.statement();
            print(P);
        """)
        self.assertEqual(result["objects"], [])
        self.reject("""
            class Specification{}
            constructor func Specification.statement() Prop{}
            const Prop P=Specification.statement();
            P proof;
        """, "proof")

    def test_named_contract_evidence_without_native_family(self):
        result = run_source(SCHEMA + """
            const Prop P=Any.intro(Nat,Functions.always);
            class Evidence:P{TypeDef H:((x:P.A)->P.b(x));const h:H;}
            constructor func Evidence.intro(h) Evidence {this.h=h;}
            static func H Evidence.prove{return Truth.intro();}
            P proof=Evidence.intro(Evidence.prove);
            print(proof);print(P.b(Nat(0)));
        """)
        self.assertTrue(result["output"][0].startswith("<proof Any("))
        self.assertEqual(result["output"][1], "Truth")

    def test_predicate_application_can_return_different_propositions(self):
        source = SCHEMA + """
            class Another:Prop{}
            constructor func Another.intro() Another {}
            class Box{const p:Prop;const h:p;}
            static func Functions.predicate(Box x) Prop{return x.p;}
            const Prop P=Any.intro(Box,Functions.predicate);
            class Evidence:P{TypeDef H:((x:P.A)->P.b(x));const h:H;}
            constructor func Evidence.intro(H h) Evidence {this.h=h;}
            static func H Evidence.prove{return x.h;}
        """
        result = run_source(source + """
            P witness=Evidence.intro(Evidence.prove);
            const Box first=Box{p:Truth,h:Truth.intro()};
            const Box second=Box{p:Another,h:Another.intro()};
            print(P.b(first));print(P.b(second));print(witness);
        """)
        self.assertEqual(result["output"], [
            "Truth", "Another", "<proof Any(A=Box, b=predicate)>",
        ])
        self.reject(source + "P invalid=Evidence.intro(Functions.proof);")

    def test_package_visibility_and_evidence_rule_ownership(self):
        source = """
            package logic;
public class Functions{}

            public class Truth:Prop{}
            public constructor func Truth.intro() Truth {}
            public class Any:Sort(2){public const A:Type;public TypeDef B:A->Prop;public const b:B;}
            public constructor func Any.intro(A a,B b) Prop{this.A=a;this.b=b;}
            public static func Functions.predicate(Nat n) Prop{return Truth;}
            public const Prop P=Any.intro(Nat,Functions.predicate);
            public class Evidence:P{TypeDef H:((x:P.A)->P.b(x));const h:H;}
            public constructor func Evidence.intro(h) Evidence {this.h=h;}
            public static func Functions.proof(Nat n) Truth{return Truth.intro();}
        """
        result = run_source("package client;import logic;logic.P h=logic.Evidence.intro(logic.Functions.proof);print(logic.P.A);", {"logic": source})
        self.assertEqual(result["output"], ["Nat"])
        self.reject("package client;import logic;class NewRule:logic.P{}", "proposition's package", {"logic": source})
        private_metadata = source.replace("public const A:Type", "const A:Type")
        self.reject("package client;import logic;print(logic.P.A);", "Private proposition metadata", {"logic": private_metadata})

    def test_recursive_type_production_cannot_define_an_evidence_target(self):
        for argument in ("n", "n+1"):
            self.reject(f"""
                class Functions{{}}
                static func Functions.loop(Int n) Prop{{return Functions.loop({argument});}}
                const Prop P=Functions.loop(1);
                class Evidence:P{{}}
            """, "Cyclic type-level")

    def test_recursive_predicates_cannot_enter_generated_metadata(self):
        self.reject(SCHEMA + """
            static func Functions.loop(Nat n) Prop{return Functions.loop(n);}
            const Prop P=Any.intro(Nat,Functions.loop);
            print(P);
        """, "Cyclic type-level")

    def test_beta_and_delta_equal_predicates_have_the_same_generated_type(self):
        result = run_source(SCHEMA + """
            static func Functions.again(Nat n) Prop{return Truth;}
            const Prop P=Any.intro(Nat,Functions.always);
            const Prop Q=Any.intro(Nat,Functions.again);
            const Prop R=Any.intro(Nat,Functions.always);
            print(P==Q);print(P==R);
        """)
        self.assertEqual(result["output"], ["true", "true"])

    def test_nested_type_function_calls_are_not_mistaken_for_recursion(self):
        result = run_source(SCHEMA + """
            static func Functions.id(Type A) Type{return A;}
            const Prop P=Any.intro(Functions.id(Functions.id(Nat)),Functions.always);
            print(P.A);
        """)
        self.assertEqual(result["output"], ["Nat"])

    def test_signed_static_values_normalize_without_runtime_execution(self):
        result = run_source("""
            class Tagged{const Int kind;}
            constructor func Tagged.intro(kind) Prop{this.kind=kind;}
            const Prop P=Tagged.intro(+1);
            const Prop Q=Tagged.intro(1);
            const Prop R=Tagged.intro(-1);
            print(P==Q);print(R.kind);
        """)
        self.assertEqual(result["output"], ["true", "-1"])

    def test_symbolic_generator_arguments_are_explicitly_not_implemented(self):
        self.reject("""
public class Functions{}

            class Tag{const Nat n;}
            constructor func Tag.intro(n) Prop{this.n=n;}
            static func Functions.at(Nat n) Prop{return Tag.intro(n);}
            const Prop P=Functions.at(Nat(1));
        """, "statically established field information")

    def test_stable_object_metadata_keeps_existing_reference_semantics(self):
        result = run_source("""
            class Config{Int n;}
            class Schema{const Config config;}
            constructor func Schema.intro(config) Prop{this.config=config;}
            const Config config=Config{n:7};
            const Prop P=Schema.intro(config);
            Config alias=P.config;
            print(alias.n);
            config.n=8;
            print(alias.n);print(config==alias);
        """)
        self.assertEqual(result["output"], ["7", "8", "true"])

    def test_metadata_does_not_make_mutable_object_fields_stable_type_inputs(self):
        source = """
            class Config{Int n;}
            class Schema{const Config config;}
            constructor func Schema.intro(config) Prop{this.config=config;}
            class Tagged{const Int n;}
            constructor func Tagged.intro(n) Prop{this.n=n;}
            const Config config=Config{n:7};
            const Prop P=Schema.intro(config);
        """
        for value in ("P.config.n", "(P.config).n"):
            self.reject(source + f"const Prop Q=Tagged.intro({value});")


if __name__ == "__main__":
    unittest.main()

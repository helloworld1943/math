import unittest
from pathlib import Path
from unittest.mock import patch

from .language import LanguageError, parse, run_source
from .runtime import FunctionValue, World
from .type_terms import DataType, Static


class CheckingTests(unittest.TestCase):
    def test_example_reports_fresh_named_judgments_and_transparent_aliases(self):
        result = run_source(Path(__file__).with_name("theory_example.nod").read_text())["theory"]
        repeated = [report for report in result["reports"] if report["term"] == "Box"]
        self.assertEqual(len(repeated), 2)
        self.assertNotEqual(repeated[0]["node"], repeated[1]["node"])
        self.assertEqual(repeated[0]["normal"], repeated[1]["normal"])
        self.assertEqual(repeated[0]["type"], "Sort(2)")
        self.assertTrue(any(node["kind"] == "CheckedType" for node in result["nodes"]))
        self.assertNotIn("constants", result)

    def test_explicit_formal_mode_never_executes_source_effects(self):
        source = "class Box{}Int n=0;print(1/0);while(true){n=n+1;}"
        with patch.object(World, "execute", side_effect=AssertionError("effect")):
            result = run_source(source, check_only=True)
        self.assertEqual(result["steps"], 0)
        self.assertEqual(result["variables"], {})
        self.assertEqual(result["objects"], [])
        self.assertEqual(result["output"], [])
        self.assertEqual(result["execution"], "class specification checking")
        self.assertEqual(result["theory"]["reports"], [])

    def test_explicit_formal_mode_and_check_commands_use_world(self):
        source = "class Box{}class Types{TypeDef B:Box;}check Types.B:Type;print(7);"
        direct = World(parse(source), {}).run(check_only=True)
        automatic = run_source(source)
        explicit = run_source(source, check_only=True)
        for result in (automatic, explicit):
            self.assertEqual(result["theory"], direct["theory"])
            self.assertEqual(result["output"], ["Types.B : Sort(1)"])
            self.assertEqual(result["steps"], 0)

    def test_named_canonical_scalar_types_need_no_assumptions(self):
        result = run_source("check Nat:Type;check Int:Type;check Bool:Type;check Float:Type;")
        self.assertEqual([report["term"] for report in result["theory"]["reports"]],
                         ["Nat", "Int", "Bool", "Float"])
        self.assertEqual([report["type"] for report in result["theory"]["reports"]], ["Sort(1)"] * 4)
        self.assertNotIn("constants", result["theory"])
        self.assertEqual(run_source("Nat n=2;Int i=-3;Bool b=true;Float f=1.5;")["variables"],
                         {"n": 2, "i": -3, "b": True, "f": 1.5})

    def test_named_values_are_checked_without_allocating_runtime_objects(self):
        result = run_source("class Box{Int value;}Box item=Box{value:2};check item:Box;")
        report = result["theory"]["reports"][0]
        by_id = {node["id"]: node for node in result["theory"]["nodes"]}
        self.assertEqual(report["type"], "Box")
        self.assertEqual(report["normal"], "item")
        self.assertEqual(by_id[report["typeNode"]]["kind"], "CheckedType")
        self.assertEqual(result["variables"], {})
        self.assertEqual(result["objects"], [])

    def test_annotations_are_composed_before_named_type_validation(self):
        source = "class Box{}check Box:Prop;"
        self.assertTrue(parse(source).items())
        with self.assertRaisesRegex(LanguageError, "Expected Sort\\(0\\), got Sort\\(1\\)"):
            run_source(source)
        for source in (
            "class Box{value:Missing;}check Box:Type;",
            "class Box:Type{const A:Type;}check Box:Type;",
            "check Missing:Type;",
        ):
            with self.subTest(source=source):
                with self.assertRaises(LanguageError):
                    run_source(source)

    def test_checks_require_named_declarations_and_aliases(self):
        for source in (
            "check Sort(1);", "check Nat->Nat;", "check 1;",
            "class Box{}check Box{};",
        ):
            with self.subTest(source=source):
                with self.assertRaisesRegex(LanguageError, "named"):
                    run_source(source)

    def test_scalar_assumption_and_definition_keywords_are_rejected(self):
        for source in (
            "axiom N:Type;", "axiom P:Prop;axiom h:P;",
            "def Alias:Type=Nat;",
            "class Owner{TypeDef H:((x:Int)->Int);}static func H Owner.id{return x;}def f:Owner.H=Owner.id;",
        ):
            with self.subTest(source=source):
                for pipeline in (parse, run_source):
                    with self.assertRaises(LanguageError) as caught:
                        pipeline(source)
                    self.assertIn(caught.exception.stage, ("syntax", "tokenizer"))

    def test_no_source_anonymous_function_implementation(self):
        for source in (
            "check fun(x:Type)=>x;",
            "const Int->Int f=fun(x:Int)=>x;",
            "class Types{TypeDef F:(fun(T:Type)=>T)(Nat);}",
        ):
            with self.subTest(source=source):
                with self.assertRaises(LanguageError):
                    run_source(source)

    def test_aliases_unfold_without_creating_nominal_types(self):
        source = """
            class First{}
            class Second{}
            class Types{TypeDef A:First;TypeDef B:A;TypeDef C:Second;}
            check Types.A:Type;check Types.B:Type;check Types.C:Type;
        """
        result = run_source(source)
        self.assertEqual([report["normal"] for report in result["theory"]["reports"]],
                         ["First", "First", "Second"])
        self.assertEqual({item["name"] for item in result["classes"]}, {"First", "Second", "Types"})
        self.assertTrue(all(not item["fields"] for item in result["classes"]))
        self.assertEqual(run_source("class First{}class Second{}print(First==Second);")["output"],
                         ["false"])

    def test_alpha_equivalent_named_contracts_have_equal_types(self):
        world = World(parse("""
            class Contracts:Sort(2){
                TypeDef I:((T:Type)->(x:T)->T);
                TypeDef J:((U:Type)->(y:U)->U);
            }
            static func I Contracts.identity{return x;}
            const Contracts.J other=Contracts.identity;
            print(other(Nat,3));print(other(Bool,true));
        """), {})
        result = world.run()
        owner = next(class_spec for class_spec in world.classes.values() if class_spec.name == "Contracts")
        self.assertTrue(world.same_type(world.entry, owner.node, owner.aliases["I"][0], owner.aliases["J"][0]))
        self.assertEqual(result["output"], ["3", "true"])

    def test_impredicative_arrows_are_checked_inside_named_aliases(self):
        result = run_source("""
            class Contracts:Sort(4){
                TypeDef H:((T:Sort(3))->(p:Prop)->p);
            }
            check Contracts.H:Prop;
        """)
        self.assertEqual(result["theory"]["reports"][0]["type"], "Sort(0)")

    def test_named_static_normalization_and_partial_captures_materialize(self):
        world = World(parse("""
            class Truth:Prop{}constructor func Truth() Truth {}
            class Helpers:Sort(2){TypeDef H:((T:Type)->(x:T)->Prop);}
            static func H Helpers.predicate{return Truth;}
        """), {})
        world.check()
        function = next(fn for fn in world.functions if fn.name == "predicate")
        symbol = world.function_symbol(function)
        normalized = world.normalize_static(world.entry, function.node, symbol)
        self.assertEqual(normalized.kind, "lambda")
        complete = world.materialize_static(world.entry, function.node, normalized)
        self.assertIsInstance(complete, FunctionValue)
        self.assertIs(complete.function, function)
        partial = world.materialize_static(world.entry, function.node, Static(
            "call", children=(symbol, Static("type", DataType("Nat"))),
        ))
        self.assertIsInstance(partial, FunctionValue)
        self.assertEqual(partial.bound, (DataType("Nat"),))
        self.assertEqual(str(world.invoke(world.entry, function.node, partial, [3])), "Truth")
        with self.assertRaisesRegex(LanguageError, "Unsupported runtime projection"):
            world.materialize_static(world.entry, function.node, Static(
                "lambda", (), (Static("literal", 0),),
            ))

    def test_dependent_identity_is_constructed_as_a_class_field(self):
        result = run_source("""
            class Identity:Sort(2){
                const A:Type;TypeDef Apply:A->A;
                TypeDef I:((T:Type)->(x:T)->T);const apply:Apply;
            }
            static func I Identity.identity{return x;}
            constructor func Identity(A a) Identity {this.A=a;this.apply=Identity.identity(a);}
            const Identity natural=Identity(Nat);
            const Identity boolean=Identity(Bool);
            print(natural.apply(5));print(boolean.apply(true));
        """)
        self.assertEqual(result["output"], ["5", "true"])
        self.assertNotIn("theory", result)

    def test_current_formal_checker_work_budget_is_enforced(self):
        world = World(parse("class Box{}check Box:Type;"), {})
        world.type_steps = 30_000
        with self.assertRaisesRegex(LanguageError, "work budget"):
            world.run(check_only=True)

    def test_verified_judgment_links_are_real_ordered_slots(self):
        result = run_source("class Types{TypeDef N:Nat;}check Types.N:Type;")
        graph = result["theory"]
        by_id = {node["id"]: node for node in graph["nodes"]}
        for node in graph["nodes"]:
            self.assertEqual(len(set(node["outputs"])), len(node["outputs"]))
            self.assertNotIn("contextDependent", node)
            for target in node["outputs"]:
                self.assertLess(by_id[target]["position"], node["position"])
            for child, slot in zip(node["children"], node["childSlots"]):
                self.assertEqual(node["outputs"][slot], child)
        for report in graph["reports"]:
            self.assertIn(report["source"], {node["id"] for node in result["nodes"]})
            self.assertEqual(by_id[report["annotation"]]["kind"], "Annotation")
            self.assertEqual(by_id[report["typeNode"]]["kind"], "Sort")


if __name__ == "__main__":
    unittest.main()

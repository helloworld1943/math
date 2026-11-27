import unittest
from pathlib import Path

from .language import LanguageError, MAX_SOURCE, parse, run_source
from .runtime import World


class LanguageTests(unittest.TestCase):
    def test_func_is_the_keyword_for_functions_and_methods(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.add(Int x) Int{return x+1;}
            class X{Int n;}
            func X.get() Int{return this.n;}
            X x=X{n:2};print(Functions.add(x.get()));
        """), ["3"])
        self.reject("function Int old(){return 1;}", stage="syntax")
        self.assertEqual(self.output("Int function=1;print(function);"), ["1"])

    def test_explicit_item_statement_and_expression_categories(self):
        program = parse("if(true){Int x=5;print((x));}")
        syntax = program.description(program.final).children[0]
        item = program.description(syntax).children[0]
        self.assertEqual(program.description(item).kind, "item")
        statement = program.description(item).children[0]
        self.assertEqual(program.description(statement).kind, "statement")
        conditional = program.description(statement).children[0]
        block = program.description(conditional).children[1]
        nested = program.description(block).children[0]
        self.assertEqual(program.description(nested).kind, "statement")
        declaration = program.description(nested).children[0]
        self.assertEqual(program.description(declaration).kind, "declaration")
        expression = program.description(declaration).children[2]
        kinds = []
        while len(program.description(expression).children) == 1:
            kinds.append(program.description(expression).kind)
            expression = program.description(expression).children[0]
        self.assertEqual(kinds, [
            "expression", "arrow_expr", "or_expr", "and_expr", "equality", "comparison",
            "sum", "product", "unary", "postfix", "integer",
        ])
        self.assertEqual(self.output("if(true){Int x=5;print((x));}"), ["5"])

    def test_wrappers_have_types_and_do_not_add_execution_steps(self):
        result = run_source("print(1+2);")
        self.assertEqual(result["output"], ["3"])
        self.assertEqual(result["steps"], 4)
        wrappers = [
            node for node in result["nodes"]
            if node["kind"] in ("expression", "or_expr", "and_expr", "sum", "product")
        ]
        self.assertTrue(wrappers)
        self.assertTrue(all(node["type"] == "Int" for node in wrappers))
        self.assertEqual(self.output("print(-(+2));print(!false);"), ["-2", "true"])

    def output(self, source):
        return run_source(source)["output"]

    def reject(self, source, stage="type", message=None):
        with self.assertRaises(LanguageError) as caught:
            run_source(source)
        self.assertEqual(caught.exception.stage, stage)
        if message:
            self.assertIn(message, caught.exception.message)
        return caught.exception

    def test_complete_example(self):
        source = Path(__file__).with_name("example.nod").read_text()
        self.assertEqual(self.output(source), ["0", "-5", "true", "1.5", "10", "10", "20", "120"])

    def test_original_duplicate_x_is_an_error(self):
        error = self.reject("Int x = 5;\nBool x = true;", message="declaration 'x'")
        self.assertEqual(error.line, 2)

    def test_empty_program(self):
        result = run_source("")
        self.assertEqual(result["output"], [])
        self.assertEqual(result["variables"], {})
        self.assertEqual(result["tokens"], [])

    def test_boolean_operators_and_precedence(self):
        self.assertEqual(self.output("""
            Bool x = true; Bool z = x | x; print(z);
            print(false || true && false);
            print(true & !false); print(true != false);
            print((true || false) == true);
        """), ["true", "false", "true", "true", "true"])

    def test_integer_operators_and_precedence(self):
        self.assertEqual(self.output("""
            print(1 + 2 * 3); print((1 + 2) * 3);
            print(-7 / 3); print(-7 % 3); print(7 % -3);
            print(+5); print(3 <= 4); print(4 >= 4);
            print(3 < 4); print(4 > 3); print(5 - 2 - 1);
        """), ["7", "9", "-2", "-1", "1", "5", "true", "true", "true", "true", "2"])

    def test_every_integer_bitwise_boolean_mismatch_is_rejected(self):
        for expression in ("1 | 2", "true + false", "true < 2", "1 == true", "!1", "-true"):
            with self.subTest(expression=expression):
                self.reject(f"print({expression});")

    def test_declaration_assignment_and_initializer_types(self):
        self.assertEqual(self.output("Int x=1; x=x+2; print(x);"), ["3"])
        self.reject("Int x=true;")
        self.reject("Bool x=1;")
        self.reject("Int x=1; x=false;")
        self.reject("x=3;", message="Unknown variable")
        self.reject("Int x=x;", stage="runtime", message="before initialization")

    def test_scope_and_shadowing(self):
        self.assertEqual(self.output("""
            Int x=1;
            if (true) { Int x=2; print(x); }
            print(x);
            while (x < 3) { Int copy=x; x=x+1; }
            print(x);
        """), ["2", "1", "3"])
        self.reject("if (true) { Int x=1; } print(x);", message="Unknown variable")
        self.reject("if (true) { Int x=1; Int x=2; }", message="Duplicate declaration")

    def test_function_and_optional_return_semicolon(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.xx(Bool a, Bool b) Bool { return a && b }
            print(Functions.xx(true, false));
            static func Functions.add(Int a, Int b) Int { return a+b; }
            print(Functions.add(2, 3));
        """), ["false", "5"])

    def test_zero_arguments_and_forward_calls(self):
        self.assertEqual(self.output("\npublic class Functions{public TypeDef Unary:Int->Int;}\nprint(Functions.answer()); static func Functions.answer() Int { return 42; }"), ["42"])

    def test_multiple_calls_have_independent_parameter_values(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.inc(Int x) Int { x=x+1; return x; }
            print(Functions.inc(3)); print(Functions.inc(8));
        """), ["4", "9"])

    def test_recursive_function(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.fact(Int n) Int {
                if (n <= 1) { return 1; }
                else { return n * Functions.fact(n-1); }
            }
            print(Functions.fact(5));
        """), ["120"])

    def test_bad_function_signatures_and_calls(self):
        examples = (
            ("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(Int a) Int { return a; } print(Functions.f());", "expects 1"),
            ("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(Int a) Int { return a; } print(Functions.f(1,2));", "expects 1"),
            ("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(Int a) Int { return a; } print(Functions.f(true));", "Expected Int"),
            ("print(unknown());", "Unknown function"),
            ("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(Int a, Bool a) Int { return 1; }", "parameter"),
            ("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f() Int { return 1; } static func Functions.f() Int { return 2; }", "member"),
            ("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(Int x) Int { Int x=2; return x; }", "declaration"),
        )
        for source, message in examples:
            with self.subTest(source=source):
                self.reject(source, message=message)

    def test_standalone_functions_are_rejected_without_hidden_owners(self):
        for source in (
            "func inc(Int n) Int{return n+1;}",
            "static func inc(Int n) Int{return n+1;}",
            "func show(Int n){print(n);}",
        ):
            self.assertTrue(parse(source).items())
            self.reject(source, message="class owner")

    def test_class_static_functions_are_not_instance_methods(self):
        source = """
            class Math{}
            static func Math.add(Int a,Int b) Int{return a+b;}
            static func Math.show(Int n){print(n);}
            static func Math.identity(Int n) Int {return n;}
        """
        result = run_source(source + "Math.show(Math.add(2,3));print(Math.identity(7));")
        self.assertEqual(result["output"], ["5", "7"])
        declared = [fn for fn in result["functions"] if not fn.get("implicit")]
        self.assertTrue(all(fn["static"] and fn["owner"] == "Math" for fn in declared))
        self.assertEqual({fn["name"] for fn in declared}, {"Math.add", "Math.show", "Math.identity"})
        wrappers = [node for node in result["nodes"] if node["kind"] == "static_function"]
        self.assertEqual(len(wrappers), 3)
        self.assertTrue(all(node["static"] and node["type"] for node in wrappers))
        self.reject(source + "Math m;print(m.add(1,2));")
        self.reject("class Math{}static func Math.bad() Int{return this.n;}")
        self.reject("static func Missing.f() Int{return 1;}")

    def test_static_functions_can_be_values_and_have_separate_namespaces(self):
        self.assertEqual(self.output("""
            class Helpers{TypeDef Unary:Int->Int;}
            static func Helpers.inc(Int x) Int{return x+1;}
            static func Helpers.apply(Int x,Helpers.Unary f) Int{return f(x);}
            Int inc=9;
            print(Helpers.apply(2,Helpers.inc));print(inc);
        """), ["3", "9"])

    def test_public_static_functions_expose_their_owner_and_keep_package_visibility(self):
        source = "package a;public class Helpers{public TypeDef Unary:Int->Int;}public static func Helpers.inc(Int n) Int{return n+1;}"
        self.assertEqual(run_source("package b;import a;print(a.Helpers.inc(4));", {"a": source})["output"], ["5"])
        for source_text in (
            source.replace("public static func", "static func"),
            source.replace("public class", "class"),
        ):
            with self.assertRaises(LanguageError):
                run_source("package b;import a;print(a.Helpers.inc(4));", {"a": source_text})
        self.reject("class Helpers{}public static func Helpers.inc(Int n) Int{return n;}", message="private type")
        with self.assertRaises(LanguageError):
            run_source("package b;import a;static func a.Helpers.extra() Int{return 1;}", {"a": source})

    def test_functions_can_read_package_globals(self):
        self.assertEqual(self.output("\npublic class Functions{public TypeDef Unary:Int->Int;}\nInt x=3; static func Functions.f() Int { return x; }print(Functions.f());"), ["3"])

    def test_variables_shadow_function_names_but_are_not_callable(self):
        self.reject("Int x=3; print(x());", message="not callable")
        self.reject("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.f() Int { return 1; }
            static func Functions.g(Int f) Int { return f(); }
        """, message="not callable")

    def test_return_rules(self):
        self.reject("return 1;", message="only allowed inside")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f() Int { return true; }", message="Expected Int")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f() Int { print(1); }", message="every path")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(Bool a) Int { if(a){return 1;} }", message="every path")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f() Int { while(true){return 1;} }", message="every path")
        self.assertEqual(self.output("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(Bool x) Int { if(x){return 1;}else{return 2;} } print(Functions.f(false));"), ["2"])

    def test_if_checks_both_branches_but_executes_only_one(self):
        self.assertEqual(self.output("if (false) { print(1/0); } else { print(2); }"), ["2"])
        self.reject("if (true) { print(1); } else { print(unknown); }", message="Unknown variable")
        self.reject("if (1) { print(1); }", message="Expected Bool")

    def test_while_assignment_and_wrong_guard(self):
        self.assertEqual(self.output("Int i=0; while(i<3){print(i);i=i+1;}"), ["0", "1", "2"])
        self.reject("while (1) { print(1); }", message="Expected Bool")

    def test_short_circuit_versus_eager_boolean_operators(self):
        self.assertEqual(self.output("print(false && (1/0==0)); print(true || (1/0==0));"), ["false", "true"])
        self.reject("print(false & (1/0==0));", "runtime", "Division by zero")
        self.reject("print(true | (1/0==0));", "runtime", "Division by zero")

    def test_runtime_failure_returns_no_partial_output(self):
        self.reject("print(1); print(1/0);", "runtime", "Division by zero")
        self.reject("print(1%0);", "runtime", "Division by zero")

    def test_comments_and_keyword_prefixes(self):
        self.assertEqual(self.output("""
            // true is not a variable
            Bool true_value=true; Int integer=2;
            print(true_value); print(integer); // done
        """), ["true", "2"])
        self.reject("Int true=1;", "syntax")

    def test_syntax_and_lexical_errors_are_distinct(self):
        self.reject("Int x=;", "syntax")
        self.reject("Int x=1", "syntax")
        self.reject("print(@);", "tokenizer")
        self.reject("func f() Int { return 1;", "syntax")

    def test_lowercase_builtin_aliases_are_not_source_syntax(self):
        for source in (
            "int x=1;", "bool x=true;", "class Box{int x;}",
            "class Box{}static func Box.ready() bool{return true;}",
        ):
            with self.subTest(source=source):
                self.reject(source, "tokenizer")

    def test_ordinary_function_results_follow_parameters(self):
        result = run_source("""
            class Truth:Prop{}
            constructor func Truth() Truth {}
            class Functions{}
            static func Functions.always(Nat n) Prop{return Truth;}
            static func Functions.add(Int a,Int b) Int{return a+b;}
            static func Functions.kind() Sort(1){return Nat;}
            print(Functions.always(Nat(0)));print(Functions.add(2,3));print(Functions.kind());
        """)
        self.assertEqual(result["output"], ["Truth", "5", "Nat"])
        self.assertEqual(
            {fn["name"]: fn["returns"] for fn in result["functions"] if fn["static"]},
            {"Functions.always": "Sort(0)", "Functions.add": "Int", "Functions.kind": "Sort(1)"},
        )

    def test_prefix_results_are_not_an_alternate_source_form(self):
        for source in (
            "class Box{}func Int Box.get(){return 1;}",
            "class Box{}static func Int Box.get(Int x){return x;}",
            "class Box{}static func Bool Box.ready(){return true;}",
            "class Box{}static func Sort(1) Box.kind(){return Nat;}",
        ):
            with self.subTest(source=source):
                self.reject(source, "syntax")

    def test_class_is_the_declaration_keyword_and_metadata_name(self):
        result = run_source("class Box{Int value;}constructor func Box(Int n) Box {this.value=n;}Box b=Box(4);print(b.value);")
        self.assertEqual(result["output"], ["4"])
        self.assertEqual([item["name"] for item in result["classes"]], ["Box"])
        self.assertNotIn("structs", result)
        self.assertTrue(any(node["kind"] == "class_decl" for node in result["nodes"]))
        self.assertFalse(any(node["kind"].startswith("struct_") for node in result["nodes"]))
        self.reject("struct Box{}", "tokenizer")

    def test_constructor_role_precedes_func_and_keeps_named_forms(self):
        result = run_source("""
            class Box{const Int value;}
            constructor func Box(Int n) Box{this.value=n;return this;}
            constructor func Box.special() Box {this.value=9;}
            Box b=Box(4);print(b.value);print(Box.special().value);
        """)
        self.assertEqual(result["output"], ["4", "9"])
        constructors = [fn for fn in result["functions"] if fn["constructor"]]
        self.assertEqual({fn["name"] for fn in constructors}, {"Box", "Box.special"})
        for source in (
            "class Box{}func Box constructor(){}",
            "class Box{}func Box constructor special(){}",
            "class Box{}constructor func Box special() Box{}",
            "class Box{}constructor func Box special(){}",
        ):
            self.reject(source, "syntax")

    def test_constructor_results_are_required_but_procedures_omit_results(self):
        for declaration in (
            "constructor func Box(){}",
            "constructor func Box.special(){}",
            "public constructor func Box(){}",
        ):
            with self.subTest(declaration=declaration):
                self.reject("public class Box{}" + declaration, "syntax")
        result = run_source("""
            class Box{Int n;}
            constructor func Box(Int n) Box{this.n=n;}
            func Box.show(){print(this.n);}
            static func Box.empty(){}
            Box b=Box(7);b.show();Box.empty();
        """)
        self.assertEqual(result["output"], ["7"])
        self.assertEqual({fn["returns"] for fn in result["functions"]}, {"Box", None})
        procedures = [fn for fn in result["functions"] if fn["procedure"]]
        self.assertEqual({fn["name"] for fn in procedures}, {"Box.show", "Box.empty"})
        self.assertTrue(all(fn["returns"] is None for fn in procedures))
        self.assertFalse(any("Void" in (node["type"] or "") for node in result["nodes"]))
        self.assertTrue(any(node.get("procedure") for node in result["nodes"]))

    def test_procedures_cannot_return_or_supply_useful_values(self):
        for source in (
            "class Functions{}static func Functions.show(){return 1;}",
            "class Functions{}static func Functions.show(){return true;}",
            "class Functions{}static func Functions.show(){}Int n=Functions.show();",
            "class Functions{}static func Functions.show(){}static func Functions.get() Int{return Functions.show();}",
        ):
            with self.subTest(source=source):
                self.reject(source, message="Expected")

    def test_void_is_not_a_source_type_or_declarable_name(self):
        for source in (
            "class Functions{}static func Functions.show() Void{}",
            "class Box{}constructor func Box() Void{}",
            "Void n;",
            "class Void{}",
            "class Box{TypeDef Void:Int;}",
            "Int Void=1;",
            "class Functions{}static func Functions.f(Int Void) Int{return Void;}",
        ):
            with self.subTest(source=source):
                self.reject(source, "tokenizer")

    def test_constructor_result_must_match_its_target_not_cast_this(self):
        for annotation in ("Int", "Other", "Type"):
            with self.subTest(annotation=annotation):
                self.reject(f"class Box{{}}class Other{{}}constructor func Box() {annotation}{{}}",
                            message="constructor result")
        self.reject("class Box{}constructor func Box() Box{return 1;}", message="own this instance")
        self.reject("class Box{}constructor func Box() Box{}constructor func Box() Box{}", message="Duplicate")
        self.reject("class Box{}constructor func Box.make() Box{}constructor func Box.make() Box{}", message="Duplicate")

    def test_constructor_paths_preserve_exact_package_ownership_and_visibility(self):
        package = """
            package a.b;
            public class Box{public Int n;}
            public constructor func a.b.Box(Int n) a.b.Box{this.n=n;}
            public constructor func a.b.Box.special() a.b.Box{this.n=9;}
        """
        result = run_source("package client;import a.b;print(a.b.Box(4).n);print(a.b.Box.special().n);",
                            {"a.b": package})
        self.assertEqual(result["output"], ["4", "9"])
        self.assertEqual({fn["name"] for fn in result["functions"]}, {"a.b.Box", "a.b.Box.special"})
        for declaration in (
            "constructor func a.b.Box(Int n) a.b.Box{this.n=n;}",
            "constructor func a.b.Box.extra() a.b.Box{this.n=1;}",
        ):
            with self.subTest(declaration=declaration):
                with self.assertRaises(LanguageError) as caught:
                    run_source("package client;import a.b;" + declaration, {"a.b": package})
                self.assertIn("class's package", caught.exception.message)
        for declaration in ("constructor func n() Int{}", "constructor func n.bad() Int{}"):
            self.reject("Int n=1;" + declaration, message="class's package")

    def test_constructor_description_uses_fresh_typed_path_and_result_nodes(self):
        source = "class Box{}constructor func Box() Box{}constructor func Box.make() Box{}"
        program = parse(source)
        result = run_source(source)
        constructors = [node for node in program.items() if program.description(node).kind == "constructor"]
        for constructor in constructors:
            path, parameters, result_type, body = program.description(constructor).children
            self.assertEqual([program.description(n).kind for n in (path, parameters, result_type, body)],
                             ["path", "parameters", "named_type", "block"])
            self.assertIsNot(path, program.description(result_type).children[0])
            for node in (path, parameters, result_type, body):
                self.assertLess(program.graph.position(node), program.graph.position(constructor))
            exported = next(node for node in result["nodes"] if node["id"] == constructor.number)
            self.assertTrue(exported["constructor"])
            self.assertIsNotNone(exported["type"])

    def test_limits(self):
        self.reject(" " * (MAX_SOURCE + 1), "limit")
        self.reject("print(" + "1" * 1025 + ");", "limit")
        self.reject("print(" + "(" * 81 + "1" + ")" * 81 + ");", "limit")
        self.reject("while(true){}", "runtime", "steps")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f() Int { return Functions.f(); } print(Functions.f());", "runtime")
        self.reject("Int n=2; while(true){n=n*n;}", "runtime", "resource budget")

    def test_grammar_can_be_built_before_type_checking(self):
        program = parse("Int x=true;")
        self.assertEqual(program.description(program.final).kind, "Program")
        with self.assertRaises(LanguageError):
            World(program, {}).check()

    def test_all_description_dependencies_are_real_earlier_links(self):
        program = parse("Bool x=true; Bool z=x|x; print(z);")
        for node in program.graph.node_order:
            info = program.description(node)
            targets = tuple(
                program.graph.get_output(node, slot)
                for slot in range(program.graph.get_output_count(node))
            )
            self.assertEqual(len(set(targets)), len(targets))
            for child, slot in zip(info.children, info.slots):
                self.assertIs(targets[slot], child)
            for target in targets:
                self.assertLess(program.graph.position(target), program.graph.position(node))
            if info.token:
                self.assertIsInstance(node.value, bytes)
            else:
                self.assertIsNone(node.value)

    def test_final_node_reaches_the_entire_graph_including_punctuation(self):
        program = parse("Int x=5; print(x);")
        pending, reached = [program.final], set()
        while pending:
            node = pending.pop()
            if node in reached:
                continue
            reached.add(node)
            pending.extend(
                target for target in (
                    program.graph.get_output(node, slot)
                    for slot in range(program.graph.get_output_count(node))
                ) if target is not None
            )
        self.assertEqual(reached, program.graph.nodes)
        self.assertIn(b";", [node.value for node in program.tokens])

    def test_token_occurrences_keep_order_and_repeated_spellings(self):
        program = parse("Int x=5; print(x);")
        spellings = [program.text(node) for node in program.tokens]
        self.assertEqual(spellings, ["Int", "x", "=", "5", ";", "print", "(", "x", ")", ";"])
        occurrences = [node for node in program.tokens if node.value == b"x"]
        self.assertEqual(len(occurrences), 2)
        self.assertIsNot(occurrences[0], occurrences[1])

    def test_values_are_in_the_node_layer_not_a_payload_sidecar(self):
        program = parse("print(123);")
        literal = next(node for node in program.tokens if node.value == b"123")
        self.assertEqual(literal.value, b"123")
        self.assertFalse(hasattr(program.description(literal), "value"))

    def test_run_export_matches_graph_and_runtime_separation(self):
        result = run_source("Int x=1; x=2; print(x);")
        self.assertEqual(result["variables"], {"x": 2})
        self.assertIn("1", [node["text"] for node in result["nodes"]])
        self.assertIn("2", [node["text"] for node in result["nodes"]])
        self.assertTrue(any(node["binding"] is not None for node in result["nodes"]))
        self.assertTrue(all("contextDependent" not in node for node in result["nodes"]))
        self.assertEqual(result["nodes"][-1]["id"], result["final"])


if __name__ == "__main__":
    unittest.main()

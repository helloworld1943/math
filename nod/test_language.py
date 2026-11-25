import unittest
from pathlib import Path

from .language import Checker, LanguageError, MAX_SOURCE, parse, run_source


class LanguageTests(unittest.TestCase):
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
        self.assertEqual(self.output(source), ["true", "false", "11", "0", "1", "2", "42"])

    def test_original_duplicate_x_is_an_error(self):
        error = self.reject("int x = 5;\nbool x = true;", message="Duplicate declaration 'x'")
        self.assertEqual(error.line, 2)

    def test_empty_program(self):
        result = run_source("")
        self.assertEqual(result["output"], [])
        self.assertEqual(result["variables"], {})
        self.assertEqual(result["tokens"], [])

    def test_boolean_operators_and_precedence(self):
        self.assertEqual(self.output("""
            bool x = true; bool z = x | x; print(z);
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
        self.assertEqual(self.output("int x=1; x=x+2; print(x);"), ["3"])
        self.reject("int x=true;")
        self.reject("bool x=1;")
        self.reject("int x=1; x=false;")
        self.reject("x=3;", message="Unknown variable")
        self.reject("int x=x;", message="Unknown variable")

    def test_scope_and_shadowing(self):
        self.assertEqual(self.output("""
            int x=1;
            if (true) { int x=2; print(x); }
            print(x);
            while (x < 3) { int copy=x; x=x+1; }
            print(x);
        """), ["2", "1", "3"])
        self.reject("if (true) { int x=1; } print(x);", message="Unknown variable")
        self.reject("if (true) { int x=1; int x=2; }", message="Duplicate declaration")

    def test_function_and_optional_return_semicolon(self):
        self.assertEqual(self.output("""
            func xx(bool a, bool b) bool { return a && b }
            print(xx(true, false));
            func add(int a, int b) int { return a+b; }
            print(add(2, 3));
        """), ["false", "5"])

    def test_zero_arguments_and_forward_calls(self):
        self.assertEqual(self.output("print(answer()); func answer() int { return 42; }"), ["42"])

    def test_multiple_calls_have_independent_parameter_values(self):
        self.assertEqual(self.output("""
            func inc(int x) int { x=x+1; return x; }
            print(inc(3)); print(inc(8));
        """), ["4", "9"])

    def test_recursive_function(self):
        self.assertEqual(self.output("""
            func fact(int n) int {
                if (n <= 1) { return 1; }
                else { return n * fact(n-1); }
            }
            print(fact(5));
        """), ["120"])

    def test_bad_function_signatures_and_calls(self):
        examples = (
            ("func f(int a) int { return a; } print(f());", "expects 1"),
            ("func f(int a) int { return a; } print(f(1,2));", "expects 1"),
            ("func f(int a) int { return a; } print(f(true));", "Expected int"),
            ("print(unknown());", "Unknown function"),
            ("func f(int a, bool a) int { return 1; }", "Duplicate parameter"),
            ("func f() int { return 1; } func f() int { return 2; }", "Duplicate function"),
            ("func f() int { return 1; } int f=3;", "Duplicate declaration"),
            ("func f(int x) int { int x=2; return x; }", "Duplicate declaration"),
        )
        for source, message in examples:
            with self.subTest(source=source):
                self.reject(source, message=message)

    def test_functions_do_not_capture_top_level_runtime_variables(self):
        self.reject("int x=3; func f() int { return x; }", message="Unknown variable")

    def test_variables_shadow_function_names_but_are_not_callable(self):
        self.reject("int x=3; print(x());", message="not callable")
        self.reject("""
            func f() int { return 1; }
            func g(int f) int { return f(); }
        """, message="not callable")

    def test_return_rules(self):
        self.reject("return 1;", message="only allowed inside")
        self.reject("func f() int { return true; }", message="Expected int")
        self.reject("func f() int { print(1); }", message="every path")
        self.reject("func f(bool a) int { if(a){return 1;} }", message="every path")
        self.reject("func f() int { while(true){return 1;} }", message="every path")
        self.assertEqual(self.output("func f(bool x) int { if(x){return 1;}else{return 2;} } print(f(false));"), ["2"])

    def test_if_checks_both_branches_but_executes_only_one(self):
        self.assertEqual(self.output("if (false) { print(1/0); } else { print(2); }"), ["2"])
        self.reject("if (true) { print(1); } else { print(unknown); }", message="Unknown variable")
        self.reject("if (1) { print(1); }", message="Expected bool")

    def test_while_assignment_and_wrong_guard(self):
        self.assertEqual(self.output("int i=0; while(i<3){print(i);i=i+1;}"), ["0", "1", "2"])
        self.reject("while (1) { print(1); }", message="Expected bool")

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
            bool true_value=true; int integer=2;
            print(true_value); print(integer); // done
        """), ["true", "2"])
        self.reject("int true=1;", "syntax")

    def test_syntax_and_lexical_errors_are_distinct(self):
        self.reject("int x=;", "syntax")
        self.reject("int x=1", "syntax")
        self.reject("print(@);", "tokenizer")
        self.reject("func f() int { return 1;", "syntax")

    def test_limits(self):
        self.reject(" " * (MAX_SOURCE + 1), "limit")
        self.reject("print(" + "1" * 257 + ");", "limit")
        self.reject("print(" + "(" * 81 + "1" + ")" * 81 + ");", "limit")
        self.reject("while(true){}", "runtime", "steps")
        self.reject("func f() int { return f(); } print(f());", "runtime")
        self.reject("int n=2; while(true){n=n*n;}", "runtime", "4096 bits")

    def test_grammar_can_be_built_before_type_checking(self):
        program = parse("int x=true;")
        self.assertEqual(program.description(program.final).kind, "Program")
        with self.assertRaises(LanguageError):
            Checker(program).check()

    def test_all_description_dependencies_are_real_earlier_links(self):
        program = parse("bool x=true; bool z=x|x; print(z);")
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
        program = parse("int x=5; print(x);")
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
        program = parse("int x=5; print(x);")
        spellings = [program.text(node) for node in program.tokens]
        self.assertEqual(spellings, ["int", "x", "=", "5", ";", "print", "(", "x", ")", ";"])
        occurrences = [node for node in program.tokens if node.value == b"x"]
        self.assertEqual(len(occurrences), 2)
        self.assertIsNot(occurrences[0], occurrences[1])

    def test_values_are_in_the_node_layer_not_a_payload_sidecar(self):
        program = parse("print(123);")
        literal = next(node for node in program.tokens if node.value == b"123")
        self.assertEqual(literal.value, b"123")
        self.assertFalse(hasattr(program.description(literal), "value"))

    def test_run_export_matches_graph_and_runtime_separation(self):
        result = run_source("int x=1; x=2; print(x);")
        self.assertEqual(result["variables"], {"x": 2})
        self.assertIn("1", [node["text"] for node in result["nodes"]])
        self.assertIn("2", [node["text"] for node in result["nodes"]])
        self.assertTrue(any(node["binding"] is not None for node in result["nodes"]))
        self.assertEqual(result["nodes"][-1]["id"], result["final"])


if __name__ == "__main__":
    unittest.main()

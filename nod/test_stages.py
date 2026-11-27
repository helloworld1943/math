import unittest
from collections import defaultdict

from .language import LanguageError, export_program, inspect_stage, make_parser, parse, run_source, tokenize
from .rules import rule_graphs


class StageTests(unittest.TestCase):
    def test_tokenizer_does_not_require_valid_grammar(self):
        program = tokenize("Int x = ;")
        self.assertEqual([program.text(node) for node in program.tokens], ["Int", "x", "=", ";"])
        self.assertEqual(program.description(program.final).kind, "TokenSequence")
        self.assertEqual(
            {program.description(node).kind for node in program.graph.node_order if node not in program.tokens},
            {"Root", "TokenSequence"},
        )
        with self.assertRaises(LanguageError) as caught:
            parse("Int x = ;")
        self.assertEqual(caught.exception.stage, "syntax")

    def test_tokenizer_still_rejects_bad_characters(self):
        with self.assertRaises(LanguageError) as caught:
            tokenize("print(@);")
        self.assertEqual(caught.exception.stage, "tokenizer")

    def test_grammar_inspection_neither_checks_types_nor_executes(self):
        for source in ("Int x=true;", "print(unknown);", "print(1/0);", "while(true){}"):
            result = inspect_stage(source, syntax=True)
            self.assertNotIn("output", result)
            self.assertNotIn("variables", result)
            self.assertTrue(all(node["type"] is None and node["binding"] is None for node in result["nodes"]))
            with self.assertRaises(LanguageError):
                run_source(source)

    def test_tokenizer_and_parser_preserve_the_same_token_occurrences(self):
        source = "Int x=5; Bool z=true; print(x); // comment"
        lexical, syntax = tokenize(source), parse(source)
        self.assertEqual(
            [(lexical.description(node).kind, node.number, node.value) for node in lexical.tokens],
            [(syntax.description(node).kind, node.number, node.value) for node in syntax.tokens],
        )
        self.assertEqual(
            export_program(syntax)["tokens"], inspect_stage(source, syntax=True)["tokens"],
        )

    def test_empty_stages_are_valid(self):
        for syntax in (False, True):
            result = inspect_stage("", syntax=syntax)
            self.assertEqual(result["tokens"], [])
            self.assertTrue(result["nodes"])

    def test_lexical_and_size_limits_still_apply_to_tokenizer(self):
        for source in (" " * 32001, "1" * 1025):
            with self.assertRaises(LanguageError) as caught:
                inspect_stage(source, syntax=False)
            self.assertEqual(caught.exception.stage, "limit")


class RuleGraphTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parser = make_parser()
        cls.rules = rule_graphs()

    def test_every_token_rule_matches_actual_lark_terminal(self):
        actual = self.rules["tokenizer"]["rules"]
        self.assertEqual(len(actual), len(self.parser.terminals))
        for shown, terminal in zip(actual, self.parser.terminals):
            self.assertEqual(shown["name"], terminal.name)
            self.assertEqual(shown["pattern"], terminal.pattern.value)
            self.assertEqual(shown["patternKind"], terminal.pattern.type)
            self.assertEqual(shown["priority"], terminal.priority)
            self.assertEqual(shown["ignored"], terminal.name in self.parser.ignore_tokens)
        self.assertTrue(any(rule["name"] == "INTEGER" for rule in actual))
        self.assertTrue(any(rule["name"] == "NAME" for rule in actual))
        self.assertFalse(any(rule["name"] in ("INT", "BOOL", "AXIOM", "DEF") for rule in actual))
        self.assertTrue(any(rule["ignored"] for rule in actual))

    def test_every_grammar_alternative_matches_actual_compiled_production(self):
        grouped = defaultdict(list)
        for rule in self.parser.rules:
            grouped[str(rule.origin.name)].append({
                "symbols": [{"name": str(part.name), "terminal": part.is_term} for part in rule.expansion],
                "alias": str(rule.alias) if rule.alias is not None else None,
                "inline": rule.options.expand1,
            })
        shown = self.rules["grammar"]["rules"]
        self.assertEqual({rule["name"] for rule in shown}, set(grouped))
        for rule in shown:
            self.assertEqual(rule["alternatives"], grouped[rule["name"]])
        self.assertTrue(any(rule["helper"] for rule in shown))
        self.assertTrue(any("-> binary" in rule["source"] for rule in shown))
        self.assertFalse({"axiom", "definition", "legacy_result"} & set(grouped))
        self.assertTrue(any(rule["name"] == "result_type" for rule in shown))

    def test_no_grammar_rule_conditionally_inlines_its_category(self):
        self.assertTrue(all(not rule.options.expand1 for rule in self.parser.rules))
        self.assertTrue(all(
            not alternative["inline"]
            for rule in self.rules["grammar"]["rules"]
            for alternative in rule["alternatives"]
        ))

    def test_rule_graphs_have_real_bytes_and_valid_backward_links(self):
        for stage in ("tokenizer", "grammar"):
            graph = self.rules[stage]["graph"]
            by_id = {node["id"]: node for node in graph["nodes"]}
            for node in graph["nodes"]:
                self.assertEqual(node["value"], list(node["text"].encode()) if node["text"] is not None else None)
                self.assertEqual(len(set(node["outputs"])), len(node["outputs"]))
                if node["id"]:
                    self.assertEqual(node["outputs"][0], 0)
                for target in node["outputs"]:
                    self.assertLess(by_id[target]["position"], node["position"])
                for child, slot in zip(node["children"], node["childSlots"]):
                    self.assertEqual(node["outputs"][slot], child)
            reached, pending = set(), [graph["final"]]
            while pending:
                current = pending.pop()
                if current in reached:
                    continue
                reached.add(current)
                pending.extend(by_id[current]["outputs"])
            self.assertEqual(reached, set(by_id))

    def test_recursive_rules_reference_shared_symbols_without_graph_cycles(self):
        grammar = self.rules["grammar"]
        rule = next(rule for rule in grammar["rules"] if rule["name"] == "or_expr")
        by_id = {node["id"]: node for node in grammar["graph"]["nodes"]}
        self.assertEqual(by_id[rule["symbol"]]["text"], "or_expr")
        pending, reached = [rule["node"]], set()
        while pending:
            current = pending.pop()
            if current in reached:
                continue
            reached.add(current)
            pending.extend(by_id[current]["outputs"])
        self.assertIn(rule["symbol"], reached)
        self.assertTrue(any(part["name"] == "or_expr" for alt in rule["alternatives"] for part in alt["symbols"]))

    def test_graph_rule_metadata_agrees_with_its_pattern_and_action_nodes(self):
        for stage in ("tokenizer", "grammar"):
            data = self.rules[stage]
            by_id = {node["id"]: node for node in data["graph"]["nodes"]}
            for rule in data["rules"]:
                node = by_id[rule["node"]]
                self.assertEqual(node["children"][0], rule["symbol"])
                if stage == "tokenizer":
                    _, pattern, priority, behavior = [by_id[child] for child in node["children"]]
                    self.assertEqual(pattern["text"], rule["pattern"])
                    self.assertEqual(priority["text"], str(rule["priority"]))
                    self.assertEqual(behavior["text"], "skip" if rule["ignored"] else "emit")
                else:
                    alternatives = [by_id[child] for child in node["children"][1:]]
                    self.assertEqual(len(alternatives), len(rule["alternatives"]))
                    for shown, alternative in zip(alternatives, rule["alternatives"]):
                        sequence, action = [by_id[child] for child in shown["children"]]
                        self.assertEqual(
                            [by_id[child]["text"] for child in sequence["children"]],
                            [symbol["name"] for symbol in alternative["symbols"]],
                        )
                        self.assertIn(action["text"], rule["actions"])


if __name__ == "__main__":
    unittest.main()

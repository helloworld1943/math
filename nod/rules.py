"""Project Lark's actual lexer and compiled grammar definitions into Node graphs."""

from __future__ import annotations

import re
from collections import defaultdict

from node import Graph, Node

from .language import GRAMMAR, make_parser


class RuleGraph:
    def __init__(self) -> None:
        self.graph = Graph()
        self.rows: dict[Node, dict[str, object]] = {}
        self.symbols: dict[tuple[str, str], Node] = {}
        self.rows[self.graph.root] = {
            "kind": "Root", "label": "root", "children": [], "childSlots": [],
        }

    def node(self, kind: str, label: str, children: tuple[Node, ...] = (), value: str | None = None) -> Node:
        targets = tuple(dict.fromkeys((self.graph.root, *children)))
        node = self.graph.create_node(len(targets), value=None if value is None else value.encode("utf-8"))
        for slot, target in enumerate(targets):
            self.graph.edit_link(node, slot, target)
        self.rows[node] = {
            "kind": kind, "label": label,
            "children": [child.number for child in children],
            "childSlots": [targets.index(child) for child in children],
        }
        return node

    def symbol(self, name: str, kind: str) -> Node:
        key = name, kind
        if key not in self.symbols:
            self.symbols[key] = self.node(kind, name, value=name)
        return self.symbols[key]

    def export(self, final: Node) -> dict[str, object]:
        snapshot = self.graph.commit()
        return {
            "final": final.number,
            "nodes": [
                {
                    **self.rows[node], "id": node.number, "position": position,
                    "token": False, "text": node.value.decode("utf-8") if node.value is not None else None,
                    "value": list(node.value) if node.value is not None else None,
                    "outputs": [
                        None if target is None else target.number
                        for target in (
                            snapshot.get_output(node, slot)
                            for slot in range(snapshot.get_output_count(node))
                        )
                    ],
                }
                for position, node in enumerate(snapshot.node_order)
            ],
        }


def source_rules() -> dict[str, str]:
    """Extract display excerpts only; recognition uses Lark's compiled rules."""
    excerpts: dict[str, list[str]] = {}
    current: str | None = None
    for line in GRAMMAR.splitlines():
        match = re.match(r"\??([a-z][a-z0-9_]*):", line)
        if match:
            current = match[1]
            excerpts[current] = [line]
        elif current is not None and line[:1].isspace():
            excerpts[current].append(line)
        else:
            current = None
    return {name: "\n".join(lines) for name, lines in excerpts.items()}


def rule_graphs() -> dict[str, object]:
    parser = make_parser()
    lexical, grammatical = RuleGraph(), RuleGraph()
    terminals, rules = [], []
    ignored = set(parser.ignore_tokens)
    for terminal in parser.terminals:
        name = lexical.symbol(terminal.name, "TokenCategory")
        pattern = lexical.node(
            "LiteralPattern" if terminal.pattern.type == "str" else "RegexPattern",
            "literal" if terminal.pattern.type == "str" else "regular expression",
            value=terminal.pattern.value,
        )
        priority = lexical.node("Priority", f"priority {terminal.priority}", value=str(terminal.priority))
        behavior = lexical.node(
            "TokenBehavior", "skip" if terminal.name in ignored else "emit",
            value="skip" if terminal.name in ignored else "emit",
        )
        definition = lexical.node("TokenizerRule", terminal.name, (name, pattern, priority, behavior))
        terminals.append({
            "name": terminal.name, "node": definition.number, "symbol": name.number,
            "pattern": terminal.pattern.value, "patternKind": terminal.pattern.type,
            "priority": terminal.priority, "ignored": terminal.name in ignored,
            "source": f"{terminal.name}: {terminal.pattern.value}",
            "helper": False,
        })

    grouped = defaultdict(list)
    for rule in parser.rules:
        grouped[str(rule.origin.name)].append(rule)
    excerpts = source_rules()
    for origin, alternatives in grouped.items():
        symbol = grammatical.symbol(origin, "GrammarCategory")
        branches = []
        aliases = []
        for index, rule in enumerate(alternatives):
            symbols = tuple(
                grammatical.symbol(str(part.name), "TokenCategory" if part.is_term else "GrammarCategory")
                for part in rule.expansion
            )
            sequence = grammatical.node(
                "Sequence", "empty (epsilon)" if not symbols else f"sequence {index + 1}", symbols,
            )
            action = str(rule.alias) if rule.alias is not None else (
                "inline / pass through" if rule.options.expand1 else origin
            )
            aliases.append(action)
            action_node = grammatical.node("ComposerAction", action, value=action)
            branches.append(grammatical.node("Alternative", f"alternative {index + 1}", (sequence, action_node)))
        definition = grammatical.node("GrammarRule", origin, (symbol, *branches))
        rules.append({
            "name": origin, "node": definition.number, "symbol": symbol.number,
            "source": excerpts.get(origin, "Generated by Lark from an EBNF repetition."),
            "helper": origin.startswith("__"), "actions": aliases,
            "alternatives": [
                {
                    "symbols": [{"name": str(part.name), "terminal": part.is_term} for part in rule.expansion],
                    "alias": str(rule.alias) if rule.alias is not None else None,
                    "inline": rule.options.expand1,
                }
                for rule in alternatives
            ],
        })
    tokenizer_final = lexical.node(
        "TokenizerRules", "tokenizer definitions", tuple(
            node for node in lexical.graph.node_order if lexical.rows[node]["kind"] == "TokenizerRule"
        ),
    )
    grammar_final = grammatical.node(
        "GrammarRules", "grammar definitions", tuple(
            node for node in grammatical.graph.node_order if grammatical.rows[node]["kind"] == "GrammarRule"
        ),
    )
    return {
        "tokenizer": {"graph": lexical.export(tokenizer_final), "rules": terminals},
        "grammar": {"graph": grammatical.export(grammar_final), "rules": rules},
        "start": "start",
    }

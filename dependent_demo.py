"""Untrusted example/certificate construction, separate from the checker."""

from __future__ import annotations

from dataclasses import dataclass

from dependent import Proof, check
from relations import Call, Node


@dataclass(frozen=True)
class Typed:
    term: str
    type: str
    proof: Proof


@dataclass(frozen=True)
class Scope:
    name: str
    proof: Proof
    parent: Scope | None = None
    binder: str = ""
    type: str = ""


class Examples:
    def __init__(self) -> None:
        self.graph = {f"U{n}": Node(f"sort:{n}") for n in range(5)}
        self.graph["empty"] = Node("empty")
        self.empty = Scope("empty", Proof("context_empty", ("empty",)))
        self.counter = 0

    def node(self, kind: str, **edges: str) -> str:
        self.counter += 1
        name = f"{kind}_{self.counter}"
        self.graph[name] = Node(kind, edges)
        return name

    def sort(self, scope: Scope, level: int) -> Typed:
        term, type_node = f"U{level}", f"U{level + 1}"
        return Typed(
            term, type_node,
            Proof("type_sort", (scope.name, term, type_node), (scope.proof,)),
        )

    def absent(self, scope: Scope, binder: str) -> Proof:
        if scope.parent is None:
            return Proof("absent_empty", (scope.name, binder))
        return Proof(
            "absent_next",
            (scope.name, scope.parent.name, scope.binder, scope.type, binder),
            (self.absent(scope.parent, binder),),
        )

    def extend(self, scope: Scope, binder: str, domain: Typed) -> Scope:
        self.graph.setdefault(binder, Node("binder"))
        name = self.node(
            "context", parent=scope.name, binder=binder, type=domain.term
        )
        proof = Proof(
            "context_extend",
            (name, scope.name, binder, domain.term, domain.type),
            (scope.proof, self.absent(scope, binder), domain.proof),
        )
        return Scope(name, proof, scope, binder, domain.term)

    def lookup(self, scope: Scope, binder: str) -> tuple[str, Proof]:
        if scope.parent is None:
            raise ValueError(f"No example declaration for {binder}")
        if scope.binder == binder:
            return scope.type, Proof(
                "lookup_here", (scope.name, scope.parent.name, binder, scope.type)
            )
        type_node, previous = self.lookup(scope.parent, binder)
        return type_node, Proof(
            "lookup_next",
            (
                scope.name, scope.parent.name, scope.binder, scope.type,
                binder, type_node,
            ),
            (previous,),
        )

    def reference(self, scope: Scope, binder: str) -> Typed:
        type_node, lookup = self.lookup(scope, binder)
        name = f"ref_{binder}"
        self.graph.setdefault(name, Node("reference", {"binder": binder}))
        return Typed(
            name, type_node,
            Proof(
                "type_ref", (scope.name, name, binder, type_node),
                (scope.proof, lookup),
            ),
        )

    def pi(
        self, scope: Scope, binder: str, domain: Typed,
        child: Scope, body: Typed,
    ) -> Typed:
        name = self.node("pi", binder=binder, domain=domain.term, body=body.term)
        level = max(
            int(self.graph[value].kind.split(":")[1])
            for value in (domain.type, body.type)
        )
        type_node = f"U{level}"
        return Typed(
            name, type_node,
            Proof(
                "type_pi",
                (
                    scope.name, name, binder, domain.term, body.term, child.name,
                    domain.type, body.type, type_node,
                ),
                (domain.proof, child.proof, body.proof),
            ),
        )

    def lam(
        self, scope: Scope, binder: str, domain: Typed, child: Scope,
        body: Typed, function_type: Typed,
    ) -> Typed:
        name = self.node(
            "lambda", binder=binder, domain=domain.term, body=body.term
        )
        return Typed(
            name, function_type.term,
            Proof(
                "type_lambda",
                (
                    scope.name, name, binder, domain.term, body.term,
                    function_type.term, body.type, child.name, function_type.type,
                ),
                (function_type.proof, body.proof),
            ),
        )

    def fresh(self, term: str, binder: str) -> Proof:
        node = self.graph[term]
        if node.kind.startswith("sort:"):
            return Proof("fresh_sort", (term, binder))
        if node.kind == "reference":
            return Proof("fresh_ref", (term, binder, node.edges["binder"]))
        if node.kind == "application":
            function, argument = node.edges["function"], node.edges["argument"]
            return Proof(
                "fresh_app", (term, binder, function, argument),
                (self.fresh(function, binder), self.fresh(argument, binder)),
            )
        if node.kind not in ("lambda", "pi"):
            raise ValueError(f"Unsupported example term {term}")
        local, domain, body = (
            node.edges[key] for key in ("binder", "domain", "body")
        )
        return Proof(
            f"fresh_{node.kind}", (term, binder, local, domain, body),
            (self.fresh(domain, binder), self.fresh(body, binder)),
        )

    def substitute(self, term: str, binder: str, argument: str) -> tuple[str, Proof]:
        node = self.graph[term]
        if node.kind.startswith("sort:"):
            return term, Proof("subst_sort", (term, binder, argument, term))
        if node.kind == "reference":
            target = node.edges["binder"]
            if target == binder:
                return argument, Proof(
                    "subst_hit", (term, binder, argument, argument)
                )
            return term, Proof("subst_miss", (term, binder, argument, term, target))
        if node.kind == "application":
            function, value = node.edges["function"], node.edges["argument"]
            new_function, left = self.substitute(function, binder, argument)
            new_value, right = self.substitute(value, binder, argument)
            result = term
            if (new_function, new_value) != (function, value):
                result = self.node(
                    "application", function=new_function, argument=new_value
                )
            return result, Proof(
                "subst_app",
                (term, binder, argument, result, function, value, new_function, new_value),
                (left, right),
            )
        if node.kind not in ("lambda", "pi"):
            raise ValueError(f"Unsupported example term {term}")
        local, domain, body = (
            node.edges[key] for key in ("binder", "domain", "body")
        )
        new_domain, domain_proof = self.substitute(domain, binder, argument)
        if local == binder:
            result = term
            if new_domain != domain:
                result = self.node(
                    node.kind, binder=local, domain=new_domain, body=body
                )
            return result, Proof(
                f"subst_{node.kind}_stop",
                (term, binder, argument, result, domain, body, new_domain),
                (domain_proof,),
            )
        new_body, body_proof = self.substitute(body, binder, argument)
        result = term
        if (new_domain, new_body) != (domain, body):
            result = self.node(
                node.kind, binder=local, domain=new_domain, body=new_body
            )
        return result, Proof(
            f"subst_{node.kind}",
            (
                term, binder, argument, result, local,
                domain, body, new_domain, new_body,
            ),
            (self.fresh(argument, local), domain_proof, body_proof),
        )

    def app(self, scope: Scope, function: Typed, argument: Typed) -> Typed:
        function_type = self.graph[function.type]
        binder, domain, body = (
            function_type.edges[key] for key in ("binder", "domain", "body")
        )
        result_type, substitution = self.substitute(body, binder, argument.term)
        term = self.node(
            "application", function=function.term, argument=argument.term
        )
        return Typed(
            term, result_type,
            Proof(
                "type_app",
                (
                    scope.name, term, function.term, argument.term,
                    function.type, binder, domain, body, result_type,
                ),
                (function.proof, argument.proof, substitution),
            ),
        )

    def identity(self, scope: Scope, level: int = 0) -> Typed:
        domain = self.sort(scope, level)
        a = self.node("binder")
        under_a = self.extend(scope, a, domain)
        a_type = self.reference(under_a, a)
        x = self.node("binder")
        under_x = self.extend(under_a, x, a_type)
        inner_type = self.pi(
            under_a, x, a_type, under_x, self.reference(under_x, a)
        )
        inner = self.lam(
            under_a, x, a_type, under_x, self.reference(under_x, x), inner_type
        )
        outer_type = self.pi(scope, a, domain, under_a, inner_type)
        return self.lam(scope, a, domain, under_a, inner, outer_type)

    def ambient(self) -> Scope:
        under_n = self.extend(self.empty, "N", self.sort(self.empty, 0))
        return self.extend(under_n, "n", self.reference(under_n, "N"))

    def type_identity(self, scope: Scope) -> Typed:
        domain = self.sort(scope, 0)
        binder = self.node("binder")
        child = self.extend(scope, binder, domain)
        function_type = self.pi(
            scope, binder, domain, child, self.sort(child, 0)
        )
        return self.lam(
            scope, binder, domain, child,
            self.reference(child, binder), function_type,
        )

    def converted_example(self, scope: Scope) -> Typed:
        identity = self.type_identity(scope)
        n_type = self.reference(scope, "N")
        redex = self.app(scope, identity, n_type)
        function = self.graph[identity.term]
        binder, domain, body = (
            function.edges[key] for key in ("binder", "domain", "body")
        )
        result, substitution = self.substitute(body, binder, n_type.term)
        beta = Proof(
            "beta",
            (
                redex.term, identity.term, binder, domain,
                body, n_type.term, result,
            ),
            (substitution,),
        )
        value = self.reference(scope, "n")
        equality = Proof("equal_symm", (result, redex.term), (beta,))
        return Typed(
            value.term, redex.term,
            Proof(
                "type_convert",
                (scope.name, value.term, value.type, redex.term, redex.type),
                (value.proof, equality, redex.proof),
            ),
        )


if __name__ == "__main__":
    examples = Examples()
    scope = examples.ambient()
    identity = examples.identity(scope)
    specialized = examples.app(scope, identity, examples.reference(scope, "N"))
    applied = examples.app(scope, specialized, examples.reference(scope, "n"))
    checked = check(
        examples.graph, applied.proof,
        Call("Typing", (scope.name, applied.term, "ref_N")),
    )
    print("VALID: ((lambda A : Sort 0. lambda x : A. x) N) n : N")
    print(f"Checked {checked.proof_steps} explicit proof steps.")
    print(f"The root relation exposes {checked.explicit_objects} graph objects.")
    converted = examples.converted_example(scope)
    check(
        examples.graph, converted.proof,
        Call("Typing", (scope.name, converted.term, converted.type)),
    )
    print("VALID: n : ((lambda A : Sort 0. A) N), using a supplied beta-equality proof.")

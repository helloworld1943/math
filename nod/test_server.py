import json
import threading
import unittest
from http.client import HTTPConnection
from http.server import ThreadingHTTPServer

from .server import Handler


class QuietHandler(Handler):
    def log_message(self, format, *args):
        pass


class ServerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.server = ThreadingHTTPServer(("127.0.0.1", 0), QuietHandler)
        cls.thread = threading.Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()
        cls.port = cls.server.server_address[1]

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()
        cls.thread.join()

    def request(self, method, path, body=None, headers=None):
        connection = HTTPConnection("127.0.0.1", self.port, timeout=10)
        try:
            connection.request(method, path, body=body, headers=headers or {})
            response = connection.getresponse()
            return response.status, dict(response.getheaders()), response.read()
        finally:
            connection.close()

    def run_source(self, source):
        status, headers, body = self.request(
            "POST", "/api/run", json.dumps({"source": source}),
            {"Content-Type": "application/json"},
        )
        return status, json.loads(body)

    def test_page_and_all_assets(self):
        for path, content_type in (
            ("/", "text/html"), ("/app.js", "text/javascript"),
            ("/style.css", "text/css"), ("/example.nod", "text/plain"),
            ("/tokenizer.html", "text/html"), ("/grammar.html", "text/html"),
            ("/stage.js", "text/javascript"), ("/graph.js", "text/javascript"),
            ("/stage.css", "text/css"),
            ("/package_example.json", "application/json"),
            ("/theory.html", "text/html"), ("/theory.js", "text/javascript"),
            ("/theory_example.nod", "text/plain"),
            ("/dependent_example.nod", "text/plain"),
            ("/proposition_example.nod", "text/plain"),
        ):
            status, headers, body = self.request("GET", path)
            self.assertEqual(status, 200)
            self.assertIn(content_type, headers["Content-Type"])
            self.assertTrue(body)
            self.assertEqual(headers["Cache-Control"], "no-store")

    def test_real_language_round_trip(self):
        status, payload = self.run_source("print(2+3);")
        self.assertEqual(status, 200)
        self.assertTrue(payload["ok"])
        self.assertEqual(payload["output"], ["5"])
        self.assertEqual(payload["nodes"][-1]["id"], payload["final"])

    def test_dependent_class_example_round_trip(self):
        from pathlib import Path

        source = Path(__file__).with_name("dependent_example.nod").read_text()
        status, payload = self.run_source(source)
        self.assertEqual(status, 200, payload)
        self.assertEqual(payload["output"], ["6", "true", "4", "<proof Any>", "9", "5"])
        self.assertTrue(any(node.get("const") for node in payload["nodes"]))
        self.assertTrue(any(node.get("constructor") for node in payload["nodes"]))
        self.assertTrue(any(class_spec["sort"] == 0 for class_spec in payload["classes"]))

    def test_prop_default_nil_and_const_errors_publish_nothing(self):
        for source in (
            "class P:Prop{}P p;",
            "class P:Prop{}P p=nil;",
            "class P:Prop{}P p=P{};",
            "const Int n=1;n=2;",
            "class X{Int a;}constructor func X.make() X {}",
            "\npublic class Functions{}\nstatic func Functions.id(Type A,A x) A{return x;}",
        ):
            status, payload = self.run_source(source)
            self.assertEqual(status, 400, payload)
            self.assertEqual(payload["error"]["stage"], "type")
            self.assertNotIn("nodes", payload)
            self.assertNotIn("output", payload)

    def test_proposition_example_round_trip_separates_types_and_proofs(self):
        from pathlib import Path

        source = Path(__file__).with_name("proposition_example.nod").read_text()
        status, payload = self.run_source(source)
        self.assertEqual(status, 200, payload)
        self.assertEqual(payload["output"], [
            "Any(A=Nat, b=always)", "Nat", "Truth",
            "<proof Any(A=Nat, b=always)>", "true", "Any(A=Nat, b=never)",
            "Exists(A=Nat, b=always)", "<proof Exists(A=Nat, b=always)>", "Exists(A=Nat, b=never)",
        ])
        self.assertEqual(payload["variables"]["P"]["typeValue"], "Any(A=Nat, b=always)")
        self.assertEqual(payload["variables"]["witness"]["type"], "Any(A=Nat, b=always)")
        self.assertEqual(len(payload["generatedPropositions"]), 4)
        proposition = next(p for p in payload["generatedPropositions"] if p["schema"] == "Any" and p["evidenceSpecifications"])
        self.assertEqual(proposition["schema"], "Any")
        self.assertEqual(proposition["sort"], 0)
        self.assertEqual(proposition["evidenceSpecifications"], ["Evidence"])
        generators = [fn for fn in payload["functions"] if fn.get("generator")]
        self.assertEqual({fn["name"] for fn in generators}, {"Any", "Any.alternative", "Exists"})
        self.assertEqual({fn["name"] for fn in generators if fn["unnamed"]}, {"Any", "Exists"})
        self.assertTrue(all(fn["returns"] == "Sort(0)" for fn in generators))
        evidence = next(s for s in payload["classes"] if s["name"] == "Evidence")
        self.assertEqual(evidence["evidenceTarget"], proposition["type"])
        self.assertTrue(all(obj["prop"] and obj["fields"] == {} for obj in payload["objects"]))

    def test_unnamed_constructor_round_trip_and_invalid_calls(self):
        source = "class Box{Int n;}constructor func Box(n) Box {this.n=n;}"
        status, payload = self.run_source(source + "Box b=Box(5);print(b.n);")
        self.assertEqual(status, 200, payload)
        self.assertEqual(payload["output"], ["5"])
        self.assertEqual(payload["functions"][0]["name"], "Box")
        self.assertTrue(payload["functions"][0]["unnamed"])
        for suffix in ("Box b=Box();", "Box b=Box(true);", "constructor func Box(n) Box {this.n=n;}"):
            status, payload = self.run_source(source + suffix)
            self.assertEqual(status, 400, payload)
            self.assertEqual(payload["error"]["stage"], "type")
            self.assertNotIn("output", payload)
            self.assertNotIn("nodes", payload)

    def test_missing_results_and_legacy_constructors_publish_no_partial_results(self):
        for declaration in (
            "constructor func Box(){}",
            "constructor func Box.intro(){}",
            "constructor func Box intro() Box{}",
            "func Box constructor intro(){}",
        ):
            status, payload = self.run_source("print(1);class Box{}" + declaration)
            self.assertEqual(status, 400, payload)
            self.assertEqual(payload["error"]["stage"], "syntax")
            self.assertNotIn("output", payload)
            self.assertNotIn("nodes", payload)

    def test_procedure_api_has_no_source_void_type_or_useful_return(self):
        status, payload = self.run_source("class Functions{}static func Functions.show(Int n){print(n);}Functions.show(7);")
        self.assertEqual(status, 200, payload)
        self.assertEqual(payload["output"], ["7"])
        self.assertEqual(payload["functions"][0]["returns"], None)
        self.assertTrue(payload["functions"][0]["procedure"])
        self.assertNotIn("Void", json.dumps(payload))
        for declaration, stage in (
            ("static func Functions.show(){return 1;}", "type"),
            ("static func Functions.show() Void{}", "tokenizer"),
        ):
            status, payload = self.run_source("print(1);class Functions{}" + declaration)
            self.assertEqual(status, 400, payload)
            self.assertEqual(payload["error"]["stage"], stage)
            self.assertNotIn("output", payload)
            self.assertNotIn("nodes", payload)

    def test_standalone_funcs_publish_no_results(self):
        status, payload = self.run_source("print(1);func id(Int n) Int{return n;}")
        self.assertEqual(status, 400, payload)
        self.assertEqual(payload["error"]["stage"], "type")
        self.assertNotIn("nodes", payload)
        self.assertNotIn("output", payload)

    def test_retired_source_syntax_publishes_no_results(self):
        for source in (
            "axiom N:Type;", "def Alias:Type=Nat;", "int x=1;", "bool x=true;",
            "struct Owner{}",
            "class Owner{}static func Int Owner.id(Int x){return x;}",
            "class Owner{}func Owner constructor(){}",
            "class Owner{}static func Owner.id(Int x) Int{return (fun(y:Int)=>y)(x);}",
        ):
            for endpoint in ("/api/run", "/api/theory"):
                with self.subTest(source=source, endpoint=endpoint):
                    status, _, body = self.request("POST", endpoint, json.dumps({
                        "source": source,
                    }), {"Content-Type": "application/json"})
                    payload = json.loads(body)
                    self.assertEqual(status, 400, payload)
                    self.assertIn(payload["error"]["stage"], ("syntax", "tokenizer"))
                    self.assertTrue({"nodes", "output", "syntax", "theory"}.isdisjoint(payload))

    def test_rejected_generated_evidence_publishes_no_partial_result(self):
        from .test_generated_propositions import EVIDENCE, SCHEMA

        for suffix in (
            "P h=Evidence.intro(Nat(1));",
            "P h=nil;",
            "P.A=Bool;",
        ):
            status, payload = self.run_source("print(1);" + SCHEMA + EVIDENCE + suffix)
            self.assertEqual(status, 400, payload)
            self.assertEqual(payload["error"]["stage"], "type")
            self.assertNotIn("nodes", payload)
            self.assertNotIn("output", payload)

    def test_defaults_and_typed_nil_export_as_objects(self):
        status, payload = self.run_source("class X{Bool b;X child;}X absent=nil;X x;Bool flag;print(absent);")
        self.assertEqual(status, 200)
        self.assertTrue(payload["variables"]["absent"]["nil"])
        self.assertFalse(payload["variables"]["x"]["nil"])
        self.assertEqual(payload["variables"]["flag"], False)
        self.assertEqual(payload["objects"][0]["fields"]["b"], False)
        self.assertEqual(payload["objects"][0]["fields"]["child"], payload["variables"]["absent"])
        self.assertEqual(payload["output"], ["X(nil)"])

    def test_bare_nil_is_rejected_without_expected_type(self):
        status, payload = self.run_source("print(nil);")
        self.assertEqual(status, 400)
        self.assertEqual(payload["error"]["stage"], "type")
        self.assertIn("nil", payload["error"]["message"])
        self.assertNotIn("output", payload)
        self.assertNotIn("nodes", payload)

    def test_error_has_location_but_no_partial_graph_or_output(self):
        for source, stage in (
            ("Int x=true;", "type"), ("print(1);print(1/0);", "runtime"),
            ("Int x=;", "syntax"), ("print(@);", "tokenizer"),
        ):
            status, payload = self.run_source(source)
            self.assertEqual(status, 400)
            self.assertFalse(payload["ok"])
            self.assertEqual(payload["error"]["stage"], stage)
            self.assertIn("line", payload["error"])
            self.assertNotIn("nodes", payload)
            self.assertNotIn("output", payload)

    def test_requests_are_isolated(self):
        self.run_source("Int x=1;")
        status, payload = self.run_source("print(x);")
        self.assertEqual(status, 400)
        self.assertIn("Unknown variable", payload["error"]["message"])

    def test_rule_definition_graph_endpoint(self):
        status, _, body = self.request("GET", "/api/rules")
        self.assertEqual(status, 200)
        payload = json.loads(body)
        for stage in ("tokenizer", "grammar"):
            self.assertTrue(payload[stage]["graph"]["nodes"])
            self.assertTrue(payload[stage]["rules"])

    def test_separate_stage_boundaries(self):
        for path, source, expected_status in (
            ("/api/tokenize", "Int x=;", 200),
            ("/api/parse", "Int x=;", 400),
            ("/api/parse", "Int x=true;", 200),
            ("/api/parse", "print(1/0);", 200),
            ("/api/parse", "while(true){}", 200),
            ("/api/tokenize", "print(@);", 400),
        ):
            status, _, body = self.request("POST", path, json.dumps({"source": source}), {"Content-Type": "application/json"})
            payload = json.loads(body)
            self.assertEqual(status, expected_status, payload)
            self.assertNotIn("output", payload)
            if expected_status == 200:
                self.assertTrue(payload["ok"])
                self.assertTrue(payload["nodes"])

    def test_removed_modes_are_rejected(self):
        status, _, _ = self.request("POST", "/api/run", json.dumps({
            "source": "print(1);", "modes": {"tokenizer": "equal"},
        }), {"Content-Type": "application/json"})
        self.assertEqual(status, 400)
        self.assertEqual(self.request("GET", "/modes.js")[0], 404)

    def test_package_sources_round_trip(self):
        status, _, body = self.request("POST", "/api/run", json.dumps({
            "source": "package b;import a;print(Functions.f());",
            "packages": {"a": "package a;\npublic class Functions{}\npublic static func Functions.f() Int{return 8;}"},
        }), {"Content-Type": "application/json"})
        result = json.loads(body)
        self.assertEqual(status, 200)
        self.assertEqual(result["output"], ["8"])
        self.assertEqual(set(result["packageGraphs"]), {"a", "b"})

    def test_named_formal_checks_in_main_endpoint(self):
        status, result = self.run_source("class Types{TypeDef N:Nat;}check Types.N:Type;print(1/0);")
        self.assertEqual(status, 200)
        self.assertIn("theory", result)
        self.assertEqual(result["theory"]["reports"][0]["normal"], "Nat")
        self.assertEqual(result["execution"], "class specification checking")
        self.assertEqual(result["steps"], 0)
        self.assertEqual(result["variables"], {})
        self.assertEqual(result["output"], ["Types.N : Sort(1)"])

    def test_theory_endpoint_returns_source_and_judgment_graphs(self):
        status, _, body = self.request("POST", "/api/theory", json.dumps({
            "source": "class Box{}class Types{TypeDef B:Box;}check Types.B:Type;",
        }), {"Content-Type": "application/json"})
        result = json.loads(body)
        self.assertEqual(status, 200)
        self.assertTrue(result["syntax"]["nodes"])
        self.assertTrue(result["theory"]["nodes"])
        self.assertEqual(result["theory"]["reports"][-1]["type"], "Sort(1)")
        self.assertEqual(result["theory"]["reports"][-1]["normal"], "Box")
        self.assertNotIn("constants", result["theory"])

    def test_theory_error_returns_no_partial_graphs(self):
        status, _, body = self.request("POST", "/api/theory", json.dumps({
            "source": "class Box{}check Box:Prop;",
        }), {"Content-Type": "application/json"})
        result = json.loads(body)
        self.assertEqual(status, 400)
        self.assertEqual(result["error"]["stage"], "type")
        self.assertNotIn("syntax", result)
        self.assertNotIn("theory", result)

    def test_theory_endpoint_checks_named_classes_without_effects(self):
        status, _, body = self.request("POST", "/api/theory", json.dumps({
            "source": """
                class Box:Sort(2){const A:Type;value:A;}
                class Contracts{TypeDef N:Nat;}
                check Box:Sort(2);check Contracts.N:Type;
                print(999);Int n=0;while(true){n=n+1;}
            """,
        }), {"Content-Type": "application/json"})
        result = json.loads(body)
        self.assertEqual(status, 200, result)
        self.assertEqual([report["type"] for report in result["theory"]["reports"]], ["Sort(2)", "Sort(1)"])
        graph = {node["id"]: node for node in result["theory"]["nodes"]}
        for report in result["theory"]["reports"]:
            self.assertEqual(graph[report["annotation"]]["kind"], "Annotation")
            self.assertEqual(graph[report["typeNode"]]["kind"], "Sort")
        self.assertNotIn("output", result)

    def test_invalid_class_theory_and_anonymous_terms_publish_nothing(self):
        for source in (
            "class Box:Type{const A:Type;}check Box:Type;",
            "class Box{value:Missing;}check Box:Type;",
            "class Box{TypeDef N:Nat;}check Box.N:Prop;",
            "class Box{}check Nat->Nat;",
            "check fun(x:Type)=>x;",
        ):
            status, _, body = self.request("POST", "/api/theory", json.dumps({
                "source": source,
            }), {"Content-Type": "application/json"})
            result = json.loads(body)
            self.assertEqual(status, 400, result)
            self.assertNotIn("syntax", result)
            self.assertNotIn("theory", result)

    def test_theory_requests_do_not_share_declarations(self):
        for source, expected in (("class Box{}check Box:Type;", 200), ("check Box:Type;", 400)):
            status, _, body = self.request("POST", "/api/theory", json.dumps({
                "source": source,
            }), {"Content-Type": "application/json"})
            result = json.loads(body)
            self.assertEqual(status, expected, result)
            if expected == 400:
                self.assertIn("Unknown", result["error"]["message"])
                self.assertNotIn("theory", result)

    def test_theory_endpoint_accepts_only_a_single_source(self):
        status, _, body = self.request("POST", "/api/theory", json.dumps({
            "source": "class Box{}check Box:Type;",
            "packages": {"other": "package other;public class Other{}"},
        }), {"Content-Type": "application/json"})
        result = json.loads(body)
        self.assertEqual(status, 400, result)
        self.assertEqual(result["error"]["stage"], "input")
        self.assertTrue({"syntax", "theory", "output"}.isdisjoint(result))

    def test_bad_json_and_invalid_request_shape(self):
        for body in ("{", "[]", '{"source":3}', '{"source":"","extra":1}', '{"other":""}'):
            status, _, data = self.request("POST", "/api/run", body, {"Content-Type": "application/json"})
            self.assertEqual(status, 400)
            self.assertIn("error", json.loads(data))

    def test_only_allowlisted_assets_are_served(self):
        for path in ("/language.py", "/../node/layer0.py", "/nod.md", "/unknown"):
            status, _, _ = self.request("GET", path)
            self.assertEqual(status, 404)

    def test_external_origins_and_hosts_are_rejected(self):
        for headers in (
            {"Origin": "https://example.com"},
            {"Host": "example.com"},
        ):
            status, _, _ = self.request("GET", "/", headers=headers)
            self.assertEqual(status, 403)
        status, _, _ = self.request("POST", "/api/run", '{"source":""}', {
            "Content-Type": "application/json", "Origin": "https://example.com",
        })
        self.assertEqual(status, 403)

    def test_same_origin_is_accepted(self):
        status, _, _ = self.request("POST", "/api/run", '{"source":""}', {
            "Content-Type": "application/json", "Origin": f"http://127.0.0.1:{self.port}",
        })
        self.assertEqual(status, 200)

    def test_wrong_content_type_and_oversized_body_are_rejected(self):
        status, _, _ = self.request("POST", "/api/run", "source", {"Content-Type": "text/plain"})
        self.assertEqual(status, 415)
        status, _, _ = self.request("POST", "/api/run", "", {
            "Content-Type": "application/json", "Content-Length": "150001",
        })
        self.assertEqual(status, 413)


if __name__ == "__main__":
    unittest.main()

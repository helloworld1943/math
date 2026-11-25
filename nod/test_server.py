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

    def test_error_has_location_but_no_partial_graph_or_output(self):
        for source, stage in (
            ("int x=true;", "type"), ("print(1);print(1/0);", "runtime"),
            ("int x=;", "syntax"), ("print(@);", "tokenizer"),
        ):
            status, payload = self.run_source(source)
            self.assertEqual(status, 400)
            self.assertFalse(payload["ok"])
            self.assertEqual(payload["error"]["stage"], stage)
            self.assertIn("line", payload["error"])
            self.assertNotIn("nodes", payload)
            self.assertNotIn("output", payload)

    def test_requests_are_isolated(self):
        self.run_source("int x=1;")
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
            ("/api/tokenize", "int x=;", 200),
            ("/api/parse", "int x=;", 400),
            ("/api/parse", "int x=true;", 200),
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

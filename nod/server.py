"""Loopback-only playground backed by the real Python graph language."""

from __future__ import annotations

import argparse
import json
import logging
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit

from .language import LanguageError, inspect_stage, run_source
from .rules import rule_graphs


ROOT = Path(__file__).parent
LOG = logging.getLogger(__name__)
ASSETS = {
    "/": ("playground.html", "text/html; charset=utf-8"),
    "/playground.html": ("playground.html", "text/html; charset=utf-8"),
    "/app.js": ("app.js", "text/javascript; charset=utf-8"),
    "/style.css": ("style.css", "text/css; charset=utf-8"),
    "/example.nod": ("example.nod", "text/plain; charset=utf-8"),
    "/dependent_example.nod": ("dependent_example.nod", "text/plain; charset=utf-8"),
    "/proposition_example.nod": ("proposition_example.nod", "text/plain; charset=utf-8"),
    "/tokenizer.html": ("tokenizer.html", "text/html; charset=utf-8"),
    "/grammar.html": ("grammar.html", "text/html; charset=utf-8"),
    "/stage.js": ("stage.js", "text/javascript; charset=utf-8"),
    "/graph.js": ("graph.js", "text/javascript; charset=utf-8"),
    "/stage.css": ("stage.css", "text/css; charset=utf-8"),
    "/package_example.json": ("package_example.json", "application/json; charset=utf-8"),
    "/theory.html": ("theory.html", "text/html; charset=utf-8"),
    "/theory.js": ("theory.js", "text/javascript; charset=utf-8"),
    "/theory_example.nod": ("theory_example.nod", "text/plain; charset=utf-8"),
}
MAX_BODY = 150_000


class Handler(BaseHTTPRequestHandler):
    server_version = "NodPlayground/1"

    def reply(self, status: int, data: bytes, content_type: str) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy", "default-src 'self'; style-src 'self'; script-src 'self'; object-src 'none'; frame-ancestors 'none'")
        self.end_headers()
        self.wfile.write(data)

    def json_reply(self, status: int, payload: dict[str, object]) -> None:
        self.reply(status, json.dumps(payload).encode("utf-8"), "application/json; charset=utf-8")

    def allowed(self) -> bool:
        port = self.server.server_address[1]
        hosts = {f"127.0.0.1:{port}", f"localhost:{port}"}
        host = self.headers.get("Host", "")
        origin = self.headers.get("Origin")
        return host in hosts and (origin is None or origin in {f"http://{name}" for name in hosts})

    def do_GET(self) -> None:
        if not self.allowed():
            self.json_reply(403, {"error": {"message": "Use the local playground origin"}})
            return
        path = urlsplit(self.path).path
        if path == "/api/rules":
            self.json_reply(200, rule_graphs())
            return
        if path not in ASSETS:
            self.json_reply(404, {"error": {"message": "Not found"}})
            return
        name, content_type = ASSETS[path]
        self.reply(200, (ROOT / name).read_bytes(), content_type)

    def do_POST(self) -> None:
        if not self.allowed():
            self.close_connection = True
            self.json_reply(403, {"error": {"message": "Cross-origin requests are not allowed"}})
            return
        if self.path not in ("/api/run", "/api/tokenize", "/api/parse", "/api/theory"):
            self.close_connection = True
            self.json_reply(404, {"error": {"message": "Not found"}})
            return
        if self.headers.get_content_type() != "application/json":
            self.close_connection = True
            self.json_reply(415, {"error": {"message": "Expected application/json"}})
            return
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            length = -1
        if not 0 < length <= MAX_BODY:
            self.close_connection = True
            self.json_reply(413, {"error": {"message": "Invalid or oversized request body"}})
            return
        try:
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            if not isinstance(payload, dict) or "source" not in payload or set(payload) - {"source", "packages"} or not isinstance(payload["source"], str):
                raise LanguageError("input", "Provide source text and optional package sources")
            packages = payload.get("packages", {})
            if not isinstance(packages, dict) or any(
                not isinstance(name, str) or not isinstance(source, str) for name, source in packages.items()
            ):
                raise LanguageError("input", "packages must map package names to source text")
            if self.path == "/api/run":
                result = run_source(payload["source"], packages)
            elif self.path == "/api/theory":
                if packages:
                    raise LanguageError("input", "Formal checking accepts a single source, not package sources")
                checked = run_source(payload["source"], check_only=True)
                result = {"syntax": {key: checked[key] for key in ("final", "tokens", "occurrences", "nodes")},
                          "theory": checked["theory"]}
            else:
                if packages:
                    raise LanguageError("input", "Stage inspection accepts a single source")
                result = inspect_stage(payload["source"], syntax=self.path == "/api/parse")
        except (json.JSONDecodeError, UnicodeDecodeError) as error:
            self.json_reply(400, {"ok": False, "error": {"stage": "input", "message": f"Invalid UTF-8 JSON: {error}"}})
        except LanguageError as error:
            self.json_reply(400, {"ok": False, "error": error.as_dict()})
        except Exception:
            LOG.exception("Unexpected playground request failure")
            self.json_reply(500, {"ok": False, "error": {"stage": "server", "message": "Internal error; see server log"}})
        else:
            self.json_reply(200, {"ok": True, **result})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8765)
    args = parser.parse_args()
    logging.basicConfig(level=logging.INFO)
    with ThreadingHTTPServer(("127.0.0.1", args.port), Handler) as server:
        print(f"Nod playground: http://127.0.0.1:{server.server_address[1]}", flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            print("\nStopped Nod playground.", flush=True)


if __name__ == "__main__":
    main()

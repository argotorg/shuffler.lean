"""A mock HTTP server for the tests of LeanTools.Http. It prints its port, then serves:

POST|GET /echo        200, a JSON object: method, length (bytes), body, headers
GET /status/<code>    that status, body "status <code>"
GET /sleep/<ms>       200 after <ms> milliseconds
GET /big/<n>          200, n bytes "a"
GET /redirect         302 to /echo
POST /v1/ok/chat/completions            a completion whose content is {"auth", "model", "n_messages"}
POST /v1/flaky/<key>/<n>/chat/completions  429 for the first n requests of <key>, then as ok
POST /v1/flakyra/<key>/<n>/chat/completions  429 with "Retry-After: 7" for the first n requests of <key>
POST /v1/bad/chat/completions           400 with an OpenAI error object
POST /v1/error200/<key>/<n>/<code>/chat/completions
                                        an error in HTTP 200 for n requests, then as ok
POST /v1/ask/<key>/<prompt>/<cached>/<completion>/<finish>/<delay ms>/chat/completions
                                        a counted request for the tests of `leantools ask`
GET /count/<key>                     the number of requests of <key> so far
POST /v1/script/chat/completions        the next message of the JSON list in $MOCK_SCRIPT, as a
                                        completion; each request body is appended to $MOCK_LOG
"""

import json
import os
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


script = json.load(open(os.environ["MOCK_SCRIPT"])) if os.environ.get("MOCK_SCRIPT") else []
script_lock = threading.Lock()
counts = {}
counts_lock = threading.Lock()


def count(key):
    with counts_lock:
        counts[key] = counts.get(key, 0) + 1
        return counts[key]


def completion(content):
    return json.dumps({"id": "x", "choices": [{"index": 0, "finish_reason": "stop",
        "message": {"role": "assistant", "content": content}}],
        "usage": {"prompt_tokens": 100, "completion_tokens": 10,
                  "prompt_tokens_details": {"cached_tokens": 50}}}).encode()


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):
        pass

    def reply(self, code, body, ctype="text/plain", extra=()):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        for k, v in extra:
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def handle_any(self):
        n = int(self.headers.get("Content-Length") or 0)
        body = self.rfile.read(n) if n else b""
        parts = self.path.strip("/").split("/")
        if parts[0] == "v1" and parts[-1] == "responses":
            kind = parts[1]
            req = json.loads(body)
            if kind == "responses-retry" and count(kind) == 1:
                return self.reply(429, b'{"error":{"message":"retry"}}', "application/json")
            if kind == "responses-failed":
                out = {"type": "response.failed", "response": {"error": {"message": "denied"}}}
                data = ("data: " + json.dumps(out) + "\n\n").encode()
                return self.reply(200, data, "text/event-stream")
            assert self.headers["Authorization"] == "Bearer test-token"
            assert self.headers["session_id"] == "session-1"
            assert req["store"] is False and req["stream"] is True
            assert req["prompt_cache_key"] == "session-1"
            assert req["input"][0]["role"] == "developer"
            continuing = len(req["input"]) > 2
            assert self.headers.get("x-codex-turn-state") == ("route-first" if continuing else None)
            assert "x-doex-state" not in self.headers
            if continuing:
                assert req["input"][2]["encrypted_content"] == "opaque-reasoning"
                assert req["input"][3]["phase"] == "commentary"
                assert req["input"][-1]["call_id"] == "call_1"
            output = [
                {"type": "reasoning", "id": "rs_1", "summary": [], "encrypted_content": "opaque-reasoning"},
                {"type": "message", "id": "msg_1", "role": "assistant", "phase": "commentary",
                 "status": "completed", "content": [{"type": "output_text", "text": "Check it."}]},
                {"type": "function_call", "id": "fc_1", "call_id": "call_1", "namespace": "lean",
                 "name": "check", "arguments": "{}", "status": "completed"}]
            out = {"type": "response.completed", "response": {"status": "completed", "output": output,
                "usage": {"input_tokens": 100, "input_tokens_details": {"cached_tokens": 80}, "output_tokens": 20}}}
            data = ("data: " + json.dumps(out) + "\n\n").encode()
            return self.reply(200, data, "text/event-stream", extra=[
                ("X-Codex-Turn-State", "route-replacement" if continuing else "route-first")])
        elif parts[0] == "v1" and parts[-2:] == ["chat", "completions"]:
            kind = parts[1]
            if kind == "script":
                with script_lock:
                    if os.environ.get("MOCK_LOG"):
                        with open(os.environ["MOCK_LOG"], "a") as log:
                            log.write(body.decode() + "\n")
                    message = script.pop(0) if script else {"role": "assistant", "content": "(the script has ended)"}
                # A complete response lets integration tests set finish reasons and usage.
                if "choices" in message:
                    return self.reply(200, json.dumps(message).encode(), "application/json")
                out = {"id": "s", "choices": [{"index": 0, "message": message,
                       "finish_reason": "tool_calls" if message.get("tool_calls") else "stop"}],
                       "usage": {"prompt_tokens": 1000, "completion_tokens": 100,
                                 "prompt_tokens_details": {"cached_tokens": 800}}}
                return self.reply(200, json.dumps(out).encode(), "application/json")
            if kind == "ask":
                # /v1/ask/<key>/<prompt>/<cached>/<completion>/<finish>/<delay ms>: one counted
                # request of <key>; usage as given ("nousage" for none); finish "fail" is a 500;
                # the content is "<number of messages>:<content of the last message>"
                key, ptoks, ctoks, otoks, finish, delay = parts[2:8]
                count(key)
                time.sleep(int(delay) / 1000)
                if finish == "fail":
                    return self.reply(500, b'{"error": {"message": "ask failed"}}', "application/json")
                req = json.loads(body)
                msgs = req.get("messages", [])
                out = {"id": "a", "choices": [{"index": 0, "finish_reason": finish,
                       "message": {"role": "assistant", "content": f"{len(msgs)}:{msgs[-1]['content']}",
                                   "reasoning": f"think-{len(msgs)}"}}]}
                if ptoks != "nousage":
                    out["usage"] = {"prompt_tokens": int(ptoks), "completion_tokens": int(otoks),
                                    "prompt_tokens_details": {"cached_tokens": int(ctoks)}}
                return self.reply(200, json.dumps(out).encode(), "application/json")
            if kind == "flakyra":
                key, n = parts[2], int(parts[3])
                if count(key) <= n:
                    return self.reply(429, b'{"error": {"message": "retry"}}', "application/json",
                                      (("Retry-After", "7"),))
                kind = "ok"
            if kind in ("flaky", "flaky502"):
                key, n = parts[2], int(parts[3])
                if count(key) <= n:
                    status = 502 if kind == "flaky502" else 429
                    return self.reply(status, b'{"error": {"message": "retry"}}', "application/json")
                kind = "ok"
            if kind == "bad":
                count("bad")
                return self.reply(400, b'{"error": {"message": "bad request: no model"}}', "application/json")
            if kind == "error200":
                key, n, code = parts[2], int(parts[3]), parts[4]
                if count(key) <= n:
                    if code == "malformed":
                        return self.reply(200, b"not JSON", "application/json")
                    if code == "choices":
                        return self.reply(200, b'{"choices":[]}', "application/json")
                    error = {"message": "Upstream error from DeepInfra: Internal server error"}
                    if code == "unknown":
                        error["message"] = "unknown response error"
                    elif code == "bare":
                        error["message"] = "Internal server error"
                    elif code != "missing":
                        error["code"] = code[1:] if code.startswith("s") else int(code)
                    return self.reply(200, json.dumps({"error": error}).encode(), "application/json")
            req = json.loads(body)
            content = json.dumps({"auth": self.headers.get("Authorization"), "model": req.get("model"),
                                  "n_messages": len(req.get("messages", []))})
            self.reply(200, completion(content), "application/json")
        elif parts[0] == "count":
            with counts_lock:
                self.reply(200, str(counts.get(parts[1], 0)).encode())
        elif parts[0] == "echo":
            out = {"method": self.command, "length": len(body),
                   "body": body.decode("utf-8", "replace"),
                   "headers": {k.lower(): v for k, v in self.headers.items()}}
            self.reply(200, json.dumps(out).encode(), "application/json")
        elif parts[0] == "status":
            self.reply(int(parts[1]), f"status {parts[1]}".encode())
        elif parts[0] == "sleep":
            time.sleep(int(parts[1]) / 1000)
            self.reply(200, b"slept")
        elif parts[0] == "big":
            self.reply(200, b"a" * int(parts[1]))
        elif parts[0] == "redirect":
            self.reply(302, b"", extra=[("Location", "/echo")])
        elif parts[0] == "headers":
            self.reply(200, b"", extra=[("X-Large", "x" * int(parts[1]))])
        elif parts[0] == "interim":
            self.send_response_only(100)
            self.send_header("X-Codex-Turn-State", "interim")
            self.end_headers()
            self.reply(200, b"", extra=[("X-Codex-Turn-State", "final")])
        else:
            self.reply(404, b"no such path")

    do_GET = handle_any
    do_POST = handle_any


server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
print(server.server_address[1], flush=True)
server.serve_forever()

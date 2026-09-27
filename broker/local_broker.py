"""A local stand-in for the Jev model broker used by jev-lean's ``jev?`` tactic.

It speaks the same localhost protocol (``jev-model-broker/1``): one JSON frame
per TCP connection, operations ``health``, ``rank`` and ``helpers``.  Rankers:

* ``stable``: keep the catalogue order.  This ablates the model entirely.
* ``heuristic``: hand-written preferences over tactic families and goal shape.
* ``systemone``: any server that implements TypeSafe's ``POST /v1/systemone``
  API, such as Kev or Von.  The request and the parsing of the answer are
  jev-lean's own (``jevlean/rank.py``), so this is exactly the call jev-lean
  makes to Jev, sent to a different endpoint.
* ``llm``: a local model behind llama.cpp's server.  One forward pass scores a
  single-token label per candidate, which yields a probability distribution
  over the catalogue.  That is the same kind of answer Jev returns: a choice
  with probabilities, not generated text.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import re
import socketserver
import string
import threading
import time
import urllib.request
from typing import Any

PROTOCOL = "jev-model-broker/1"
LABELS = list(string.ascii_uppercase + string.ascii_lowercase + string.digits)
MAX_FRAME = 1_000_000

SYSTEM = (
    "You are a Lean 4 proof assistant. Given a proof state and a numbered list of "
    "candidate tactics, pick the tactic most likely to lead to a complete proof. "
    "Reply with only the label of your choice."
)


class Stats:
    """Ranking-call statistics, accumulated across broker restarts in ``path``."""

    def __init__(self, path: str | None = None) -> None:
        self.path = path
        self.lock = threading.Lock()
        self.calls = 0
        self.seconds = 0.0
        self.prompt_tokens = 0
        self.failures = 0
        if path and os.path.exists(path):
            with open(path) as handle:
                previous = json.load(handle)
            self.calls = previous.get("calls", 0)
            self.seconds = previous.get("seconds", 0.0)
            self.prompt_tokens = previous.get("prompt_tokens", 0)
            self.failures = previous.get("failures", 0)

    def _write(self) -> None:
        if self.path:
            with open(self.path, "w") as handle:
                json.dump({"calls": self.calls, "seconds": self.seconds,
                           "prompt_tokens": self.prompt_tokens, "failures": self.failures}, handle)

    def fail(self) -> None:
        with self.lock:
            self.failures += 1
            self._write()

    def add(self, seconds: float, tokens: int = 0) -> None:
        with self.lock:
            self.calls += 1
            self.seconds += seconds
            self.prompt_tokens += tokens
            self._write()


def stable(context: dict, actions: list[dict]) -> list[str]:
    return [a["id"] for a in actions]


def heuristic_score(goal: str, tactic: str) -> float:
    target = goal.split("⊢")[-1]
    head = tactic.split()[0]
    score = {
        "intro": 3.0, "constructor": 2.0, "induction": 2.5, "cases": 1.5, "rcases": 1.5,
        "simp": 2.0, "rw": 2.0, "exact": 2.5, "apply": 1.5, "unfold": 1.0,
        "refine": 1.0, "left": 0.5, "right": 0.5,
    }.get(head, 0.0)
    if head == "intro" and not re.search(r"[∀→¬]", target):
        score -= 3.0
    if head == "constructor" and not re.search(r"[∧↔∃]", target):
        score -= 1.5
    if head in ("induction", "cases") and len(tactic.split()) > 1:
        variable = tactic.split()[1]
        if re.search(rf"\b{re.escape(variable)}\b", target):
            score += 1.0
        if "generalizing" in tactic:
            score -= 0.5
    if head in ("left", "right") and "∨" not in target:
        score -= 2.0
    return score


def heuristic(context: dict, actions: list[dict]) -> list[str]:
    goal = context["focused_goal"]
    ordered = sorted(enumerate(actions), key=lambda p: (-heuristic_score(goal, p[1]["tactic"]), p[0]))
    return [a["id"] for _, a in ordered]


class LlmRanker:
    def __init__(self, url: str, max_goal_chars: int, stats: Stats) -> None:
        self.url = url.rstrip("/")
        self.max_goal_chars = max_goal_chars
        self.stats = stats

    def prompt(self, context: dict, actions: list[dict]) -> str:
        goal = context["focused_goal"]
        if len(goal) > self.max_goal_chars:
            goal = goal[: self.max_goal_chars] + "\n…"
        siblings = len(context["pending_sibling_goals"])
        path = "; ".join(context["path"][-6:]) or "(none)"
        candidates = "\n".join(f"{label}. {a['tactic']}" for label, a in zip(LABELS, actions))
        user = (
            f"Proof state:\n{goal}\n\nOther open goals: {siblings}\n"
            f"Tactics applied so far: {path}\n\nCandidate tactics:\n{candidates}\n\n"
            "Which label is the best next tactic?"
        )
        return (
            f"<|im_start|>system\n{SYSTEM}<|im_end|>\n"
            f"<|im_start|>user\n{user}<|im_end|>\n<|im_start|>assistant\n"
        )

    def __call__(self, context: dict, actions: list[dict], timeout: float) -> list[str]:
        head, tail = actions[: len(LABELS)], actions[len(LABELS):]
        body = json.dumps({
            "prompt": self.prompt(context, head), "n_predict": 1, "n_probs": len(head) + 20,
            "temperature": 0.0, "cache_prompt": True, "post_sampling_probs": False,
        }).encode()
        started = time.monotonic()
        request = urllib.request.Request(f"{self.url}/completion", data=body,
                                         headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(request, timeout=max(timeout, 0.1)) as response:
            reply = json.loads(response.read())
        self.stats.add(time.monotonic() - started, reply.get("tokens_evaluated", 0))
        weights = {label: -math.inf for label in LABELS[: len(head)]}
        for entry in reply.get("completion_probabilities", [])[:1]:
            for alt in entry.get("top_logprobs", entry.get("top_probs", [])):
                token = alt.get("token", "").strip().rstrip(".")
                value = alt["logprob"] if "logprob" in alt else math.log(max(alt.get("prob", 0), 1e-30))
                if token in weights and value > weights[token]:
                    weights[token] = value
        order = sorted(range(len(head)), key=lambda i: (-weights[LABELS[i]], i))
        return [head[i]["id"] for i in order] + [a["id"] for a in tail]


# The next two functions reproduce jevlean/rank.py (payload, ranking_from_response)
# from https://github.com/jesyspa/jev-lean at 54df393 (Apache License 2.0).
JEV_MODEL = "jev-1.13.0"


def systemone_payload(context: dict, actions: list[dict], string_criteria: bool = False) -> dict:
    """jev-lean's request.  ``string_criteria`` sends each option as a plain
    string, for servers such as Von that reject jev-lean's object form."""
    criteria = {action["id"]: action["tactic"] if string_criteria else {"lean_action": action["tactic"]}
                for action in actions}
    return {
        "model": JEV_MODEL,
        "state": {"language": "Lean 4 with Mathlib", **context},
        "questions": {
            "ranking": {
                "type": "choice",
                "instructions": {
                    "question": "Which concrete Lean action is most likely to close every current goal?",
                    "constraints": ["Do not propose Lean syntax or actions outside this catalogue."],
                },
                "criteria": criteria,
            }
        },
    }


def systemone_ranking(response: Any, ids: list[str]) -> list[str]:
    answer = response.get("answers", {}).get("ranking")
    if not isinstance(answer, dict) or answer.get("type") != "choice":
        raise ValueError("response does not contain a choice answer")
    probabilities = answer.get("probabilities")
    if not isinstance(probabilities, dict) or set(probabilities) != set(ids):
        raise ValueError("response probabilities do not match the actions")
    weights = {identifier: float(probabilities[identifier]) for identifier in ids}
    # jev-lean requires the sum to be within 0.01 of 1.  Jev reports probabilities
    # rounded to two decimals, so with many options rounding alone can exceed
    # that; allow the rounding bound of 0.005 per option.
    tolerance = max(0.01, 0.005 * len(ids))
    if any(not math.isfinite(w) or w < 0.0 for w in weights.values()) or abs(sum(weights.values()) - 1.0) > tolerance:
        raise ValueError(f"response probabilities are invalid (sum {sum(weights.values()):.3f})")
    return sorted(ids, key=lambda identifier: weights[identifier], reverse=True)


class SystemOneRanker:
    """Send jev-lean's Jev request to a local /v1/systemone server."""

    def __init__(self, url: str, stats: Stats, max_actions: int, string_criteria: bool = False,
                 max_request_bytes: int = 0) -> None:
        self.string_criteria = string_criteria
        self.max_request_bytes = max_request_bytes
        self.url = url.rstrip("/")
        self.stats = stats
        self.max_actions = max_actions

    def __call__(self, context: dict, actions: list[dict], timeout: float) -> list[str]:
        head, tail = actions[: self.max_actions], actions[self.max_actions:]
        body = json.dumps(systemone_payload(context, head, self.string_criteria), ensure_ascii=False).encode()
        if self.max_request_bytes and len(body) > self.max_request_bytes:
            # Deterministic refusal, recorded as its own outcome by scripts/run.py.
            raise ValueError(f"oversize request ({len(body)} bytes > {self.max_request_bytes})")
        started = time.monotonic()
        headers = {"Content-Type": "application/json"}
        key = os.environ.get("SYSTEMONE_API_KEY")   # e.g. a TypeSafe key, to rank with Jev itself
        if key:
            headers["Authorization"] = f"Bearer {key}"
        request = urllib.request.Request(f"{self.url}/v1/systemone", data=body, headers=headers)
        with urllib.request.urlopen(request, timeout=max(timeout, 0.1)) as response:
            reply = json.loads(response.read())
        self.stats.add(time.monotonic() - started, reply.get("usage", {}).get("input_tokens", 0))
        return systemone_ranking(reply, [a["id"] for a in head]) + [a["id"] for a in tail]


class Broker:
    def __init__(self, ranker: Any, name: str, stats: Stats) -> None:
        self.ranker, self.name, self.stats = ranker, name, stats

    def handle(self, frame: dict) -> dict:
        operation = frame.get("operation")
        if operation == "health":
            return {"ok": True, "protocol": PROTOCOL, "capabilities": {"rank": True, "helpers": False}}
        if operation == "helpers":
            return {"ok": True, "proposals": [], "source": "unavailable"}
        if operation != "rank":
            return {"ok": False, "error": "unknown operation"}
        request = frame["request"]
        actions = request["actions"]
        context = {k: request[k] for k in ("focused_goal", "pending_sibling_goals", "path")}
        timeout = frame.get("deadline_ms", 5000) / 1000
        started = time.monotonic()
        try:
            if isinstance(self.ranker, (LlmRanker, SystemOneRanker)):
                ranking = self.ranker(context, actions, timeout)
            else:
                ranking = self.ranker(context, actions)
                self.stats.add(time.monotonic() - started)
            return {"ok": True, "ranking": ranking, "source": self.name}
        except Exception as error:
            self.stats.fail()
            print(f"ranking failed: {error!s:.200}", flush=True)
            if isinstance(self.ranker, SystemOneRanker):
                # Fail the task rather than silently search in catalogue order;
                # scripts/run.py does not record such tasks, so a resume retries them.
                return {"ok": False, "error": f"ranker failed: {error!s:.200}"}
            return {"ok": True, "ranking": stable(context, actions), "source": f"fallback:{error!s:.100}"}


def serve(broker: Broker, port: int) -> None:
    class Handler(socketserver.StreamRequestHandler):
        def handle(self) -> None:
            raw = self.rfile.readline(MAX_FRAME + 1)
            try:
                reply = broker.handle(json.loads(raw))
            except Exception as error:
                reply = {"ok": False, "error": str(error)[:200]}
            self.wfile.write(json.dumps(reply, ensure_ascii=False).encode() + b"\n")

    class Server(socketserver.ThreadingTCPServer):
        allow_reuse_address = True
        daemon_threads = True

    with Server(("127.0.0.1", port), Handler) as server:
        print(f"local jev broker ({broker.name}) ready on 127.0.0.1:{server.server_address[1]}", flush=True)
        server.serve_forever()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ranker", choices=["stable", "heuristic", "llm", "systemone"], required=True)
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--llm-url", default="http://127.0.0.1:8090")
    parser.add_argument("--systemone-url", default="http://127.0.0.1:8009")
    parser.add_argument("--max-actions", type=int, default=255,
                        help="candidates sent to a systemone server; the rest keep catalogue order")
    parser.add_argument("--max-request-bytes", type=int, default=0,
                        help="refuse systemone requests larger than this (0: no limit)")
    parser.add_argument("--string-criteria", action="store_true",
                        help="send candidate tactics as plain strings (needed by Von)")
    parser.add_argument("--max-goal-chars", type=int, default=6000)
    parser.add_argument("--stats", help="keep call statistics in this JSON file")
    args = parser.parse_args()
    stats = Stats(args.stats)
    ranker: Any = {"stable": stable, "heuristic": heuristic}.get(args.ranker)
    if args.ranker == "llm":
        ranker = LlmRanker(args.llm_url, args.max_goal_chars, stats)
    if args.ranker == "systemone":
        ranker = SystemOneRanker(args.systemone_url, stats, args.max_actions, args.string_criteria,
                                 args.max_request_bytes)
    serve(Broker(ranker, args.ranker, stats), args.port)


if __name__ == "__main__":
    main()

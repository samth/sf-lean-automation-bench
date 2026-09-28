"""Premise selection for waterfall: rank earlier SF theorems for each failed task.

For a task, the candidate pool is every theorem that precedes it in its chapter,
plus the theorems of the chapters it imports, most recent first, capped at
--pool.  Rankers:
  * lexical: shared identifiers between the goal and the lemma statement,
    weighted by rarity (a cheap stand-in for Lean's retrieval);
  * jev: one Jev `choice` question per task over the whole pool (TypeSafe API,
    SYSTEMONE_API_KEY); its probabilities order the pool.
It reports recall of the oracle lemmas (those the reference proof cites) in the
top k, and writes a rules file usable with ORACLE_RULES for scripts/run.py.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
import re
import sys
import urllib.request
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*")
STOP = {"theorem", "lemma", "example", "fun", "forall", "Prop", "Type", "by", "let", "in", "if", "then",
        "else", "match", "with", "true", "false", "True", "False", "Nat", "List", "Bool", "∀", "∃"}


def statement(task: dict) -> str:
    header = re.sub(r"/--.*?-/", "", task["header"], flags=re.S)
    header = re.sub(r"^\s*@\[[^\]]*\]\s*", "", header.strip())
    header = re.sub(r"^(private |protected )*theorem\s+", "", header)
    return " ".join(header.split())


def idents(text: str) -> set[str]:
    return {w.rstrip(".") for w in IDENT.findall(text)} - STOP


def chapter_imports(task: dict) -> list[str]:
    return [m.group(1) for m in re.finditer(r"^import (\S+)", task["prefix"], re.M)]


def pools(tasks: list[dict], context: str, size: int) -> dict[str, list[dict]]:
    by_chapter: dict[str, list[dict]] = {}
    for t in tasks:
        if t["context"] == context and t["kind"] == "theorem":
            by_chapter.setdefault(t["chapter"], []).append(t)
    for chapter in by_chapter.values():
        chapter.sort(key=lambda t: t["line"])
    result = {}
    for t in tasks:
        if t["context"] != context:
            continue
        earlier = [c for c in by_chapter.get(t["chapter"], []) if c["line"] < t["line"]]
        pool = list(reversed(earlier))
        for imported in chapter_imports(t):
            pool += list(reversed(by_chapter.get(imported, [])))
        seen, unique = set(), []
        for c in pool:
            if c["name"] not in seen and c["name"] != t["name"]:
                seen.add(c["name"])
                unique.append(c)
        result[t["id"]] = unique[:size]
    return result


def lexical(goal: str, pool: list[dict], df: Counter, n_docs: int) -> list[str]:
    goal_ids = idents(goal)
    def score(c: dict) -> float:
        shared = goal_ids & idents(statement(c))
        return sum(math.log(n_docs / (1 + df[w])) for w in shared)
    return [c["name"] for c in sorted(pool, key=lambda c: -score(c))]


def jev(goal: str, pool: list[dict], key: str) -> list[str]:
    ids = [f"L{i + 1}" for i in range(len(pool))]
    payload = {
        "model": "jev-1.13.0",
        "state": {"language": "Lean 4", "goal": goal},
        "questions": {"premise": {
            "type": "choice",
            "instructions": {"question": "Which previously proved lemma is most useful for proving this goal?"},
            "criteria": {i: {"lemma": f"{c['name']} : {statement(c)[:400]}"} for i, c in zip(ids, pool)},
        }},
    }
    request = urllib.request.Request("https://api.typesafe.ai/v1/systemone", data=json.dumps(payload).encode(),
                                     headers={"Content-Type": "application/json", "Authorization": f"Bearer {key}"})
    with urllib.request.urlopen(request, timeout=120) as response:
        reply = json.loads(response.read())
    probs = reply["answers"]["premise"]["probabilities"]
    order = sorted(range(len(pool)), key=lambda i: -float(probs.get(ids[i], 0.0)))
    return [pool[i]["name"] for i in order], reply.get("usage", {}).get("input_tokens", 0)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--context", default="solutions")
    parser.add_argument("--ranker", choices=["lexical", "jev"], required=True)
    parser.add_argument("--pool", type=int, default=120)
    parser.add_argument("--k", type=int, default=8)
    parser.add_argument("--sample", type=int, help="only this many tasks (random, seed 0)")
    parser.add_argument("--out", required=True, help="rules file to write (task id -> lemma names)")
    args = parser.parse_args()

    tasks = json.loads((ROOT / "tasks.json").read_text())
    oracle = json.loads((ROOT / f"experiments/oracle-lemmas.{args.context}.json").read_text())
    ids = sorted(oracle)
    if args.sample:
        random.Random(0).shuffle(ids)
        ids = sorted(ids[: args.sample])
    by_id = {t["id"]: t for t in tasks}
    all_pools = pools(tasks, args.context, args.pool)
    df = Counter(w for t in tasks if t["context"] == args.context for w in idents(statement(t)))
    n_docs = sum(1 for t in tasks if t["context"] == args.context)
    key = os.environ.get("SYSTEMONE_API_KEY", "")
    if args.ranker == "jev" and not key:
        sys.exit("jev ranker needs SYSTEMONE_API_KEY")

    rules, hits, wanted, in_pool, tokens = {}, 0, 0, 0, 0
    for i in ids:
        goal = statement(by_id[i])
        pool = all_pools[i]
        names = {c["name"] for c in pool}
        if args.ranker == "lexical":
            ranked = lexical(goal, pool, df, n_docs)
        else:
            ranked, used = jev(goal, pool, key)
            tokens += used
        top = ranked[: args.k]
        rules[i] = top
        target = [n for n in oracle[i] if n in names or n.split(".")[-1] in {x.split(".")[-1] for x in names}]
        wanted += len(oracle[i])
        in_pool += len(target)
        hits += sum(1 for n in target if n in top or n.split(".")[-1] in {x.split(".")[-1] for x in top})
    Path(args.out).write_text(json.dumps(rules, indent=1, ensure_ascii=False))
    print(f"{args.ranker}: {len(ids)} tasks, oracle lemmas {wanted}, of which in pool {in_pool}; "
          f"recall@{args.k} {hits}/{in_pool} = {hits / max(in_pool, 1):.2f}"
          + (f"; Jev input tokens {tokens}" if tokens else ""))


if __name__ == "__main__":
    main()

"""Premise selection for waterfall: which earlier SF theorems to pass as rules.

`rank` orders a candidate pool for each task and saves the full ranking;
`rules` turns rankings into a rules file (task id -> fully qualified lemma
names) for scripts/run.py's `waterfall-rules` arm (ORACLE_RULES=<file>).

Pools
  file     every theorem earlier in the task's own chapter, in file order;
  imports  `file` (most recent first) followed by the theorems of the chapters
           it imports, capped at --cap (Jev accepts at most 255 options).
Rankers
  file     no ranking: the whole `file` pool ("all previous lemmas in the file");
  lexical  identifiers shared with the goal, weighted by rarity;
  jev      one Jev `choice` question per task over the pool (TypeSafe API,
           SYSTEMONE_API_KEY); probabilities order the pool.
Names are fully qualified by tracking `namespace`/`section`/`end` in the
chapter, so they resolve wherever the target theorem sits.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import re
import sys
import urllib.request
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉!?]*")
STOP = {"theorem", "lemma", "example", "fun", "forall", "Prop", "Type", "by", "let", "in", "if", "then",
        "else", "match", "with", "true", "false", "True", "False", "Nat", "List", "Bool"}


def statement(task: dict) -> str:
    header = re.sub(r"/--.*?-/", "", task["header"], flags=re.S)
    header = re.sub(r"^\s*@\[[^\]]*\]\s*", "", header.strip())
    header = re.sub(r"^((private|protected|nonrec)\s+)*theorem\s+", "", header)
    return " ".join(header.split())


def idents(text: str) -> set[str]:
    return {w.rstrip(".") for w in IDENT.findall(text)} - STOP


def namespace_at(prefix: str) -> list[str]:
    """The namespace in effect at the end of `prefix` (sections are anonymous scopes)."""
    stack: list[tuple[str, list[str]]] = []
    for line in prefix.split("\n"):
        stripped = line.strip()
        if stripped.startswith("--"):
            continue
        m = re.match(r"^(?:namespace)\s+(\S+)", stripped)
        if m:
            stack.append(("namespace", m.group(1).split(".")))
            continue
        m = re.match(r"^(?:noncomputable\s+|public\s+|meta\s+)*section\b\s*(\S*)", stripped)
        if m and not stripped.startswith("section_"):
            stack.append(("section", []))
            continue
        m = re.match(r"^end\b\s*(\S*)$", stripped)
        if m and stack:
            stack.pop()
    return [part for kind, parts in stack for part in parts]


def full_name(task: dict) -> str | None:
    if re.match(r"^\s*(@\[[^\]]*\]\s*)?private\b", task["header"]):
        return None
    name = task["name"]
    if name.startswith("_root_."):
        return name[len("_root_."):]
    return ".".join(namespace_at(task["prefix"]) + [name])


def chapter_imports(task: dict) -> list[str]:
    return [m.group(1) for m in re.finditer(r"^(?:public\s+)?import (\S+)", task["prefix"], re.M)]


def build_pools(tasks: list[dict], context: str, cap: int) -> tuple[dict, dict]:
    by_chapter: dict[str, list[dict]] = {}
    for t in tasks:
        if t["context"] == context and t["kind"] == "theorem" and full_name(t):
            by_chapter.setdefault(t["chapter"], []).append(t)
    for chapter in by_chapter.values():
        chapter.sort(key=lambda t: t["line"])
    file_pools, import_pools = {}, {}
    for t in tasks:
        if t["context"] != context:
            continue
        earlier = [c for c in by_chapter.get(t["chapter"], []) if c["line"] < t["line"]]
        file_pools[t["id"]] = earlier
        pool = list(reversed(earlier))
        for imported in chapter_imports(t):
            pool += list(reversed(by_chapter.get(imported, [])))
        seen, unique = set(), []
        for c in pool:
            key = full_name(c)
            if key not in seen:
                seen.add(key)
                unique.append(c)
        import_pools[t["id"]] = unique[:cap]
    return file_pools, import_pools


def lexical(goal: str, pool: list[dict], df: Counter, n_docs: int) -> list[dict]:
    goal_ids = idents(goal)
    def score(c: dict) -> float:
        return sum(math.log(n_docs / (1 + df[w])) for w in goal_ids & idents(statement(c)))
    return sorted(pool, key=lambda c: -score(c))


def jev(goal: str, pool: list[dict], key: str) -> tuple[list[dict], int]:
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
    return [pool[i] for i in order], reply.get("usage", {}).get("input_tokens", 0)


def rank(args: argparse.Namespace) -> None:
    tasks = json.loads((ROOT / "tasks.json").read_text())
    by_id = {t["id"]: t for t in tasks}
    ids = [line.strip() for line in open(args.ids) if line.strip()]
    file_pools, import_pools = build_pools(tasks, args.context, args.cap)
    df = Counter(w for t in tasks if t["context"] == args.context for w in idents(statement(t)))
    n_docs = sum(1 for t in tasks if t["context"] == args.context)
    key = os.environ.get("SYSTEMONE_API_KEY", "")
    if args.ranker == "jev" and not key:
        sys.exit("jev ranker needs SYSTEMONE_API_KEY")
    out = {}
    if Path(args.out).exists():
        out = json.loads(Path(args.out).read_text())
    tokens = 0
    for n, i in enumerate(ids):
        if i in out:
            continue
        goal = statement(by_id[i])
        if args.ranker == "file":
            ranked = file_pools[i]
        elif args.ranker == "lexical":
            ranked = lexical(goal, import_pools[i], df, n_docs)
        else:
            if not import_pools[i]:
                ranked = []
            else:
                ranked, used = jev(goal, import_pools[i], key)
                tokens += used
        out[i] = [full_name(c) for c in ranked]
        if args.ranker == "jev" and n % 20 == 0:
            Path(args.out).write_text(json.dumps(out, ensure_ascii=False))
    Path(args.out).write_text(json.dumps(out, ensure_ascii=False))
    print(f"{args.ranker}: ranked {len(ids)} tasks" + (f"; Jev input tokens {tokens}" if tokens else ""))


def rules(args: argparse.Namespace) -> None:
    ranking = json.loads(Path(args.ranking).read_text())
    chosen = {i: names if args.k == 0 else names[: args.k] for i, names in ranking.items()}
    Path(args.out).write_text(json.dumps(chosen, ensure_ascii=False))
    oracle = json.loads((ROOT / f"experiments/oracle-lemmas.{args.context}.json").read_text())
    hits = wanted = 0
    for i, cited in oracle.items():
        if i not in chosen:
            continue
        tails = {n.split(".")[-1] for n in chosen[i]}
        wanted += len(cited)
        hits += sum(1 for c in cited if c.split(".")[-1] in tails)
    sizes = sorted(len(v) for v in chosen.values())
    print(f"{args.out}: median {sizes[len(sizes) // 2]} rules; recall of cited lemmas {hits}/{wanted} "
          f"= {hits / max(wanted, 1):.2f}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    r = sub.add_parser("rank")
    r.add_argument("--ranker", choices=["file", "lexical", "jev"], required=True)
    r.add_argument("--context", default="solutions")
    r.add_argument("--ids", required=True, help="task ids, one per line")
    r.add_argument("--cap", type=int, default=250)
    r.add_argument("--out", required=True)
    k = sub.add_parser("rules")
    k.add_argument("--ranking", required=True)
    k.add_argument("--k", type=int, default=0, help="top k (0: all)")
    k.add_argument("--context", default="solutions")
    k.add_argument("--out", required=True)
    args = parser.parse_args()
    (rank if args.command == "rank" else rules)(args)


if __name__ == "__main__":
    main()

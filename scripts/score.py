"""Summarize results/<arm>.<context>.jsonl into Markdown tables.

Tactic time is the task's wall time minus the same task's ``sorry`` run, which
removes the cost of elaborating the chapter prefix.
"""
from __future__ import annotations

import argparse
import json
import statistics
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ORDER = ["auto", "induct", "aesop", "jev-stable", "jev-heuristic", "jev-llm", "jev-llm7b", "jev-kev", "jev-kev4b", "jev-von", "jev-typesafe", "waterfall"]
LABELS = {
    "auto": "Automation only (`rfl`/`simp_all`/`grind`/`omega`/`decide`)",
    "induct": "Every single induction or case split, then automation",
    "aesop": "`aesop` (closest analogue of `eauto`)",
    "jev-stable": "jev-lean harness, catalogue order (no model)",
    "jev-heuristic": "jev-lean harness, hand-written ranking",
    "jev-llm": "jev-lean harness, local Qwen2.5-Coder-1.5B ranking",
    "jev-llm7b": "jev-lean harness, local Qwen2.5-Coder-7B ranking",
    "jev-kev": "jev-lean harness, Kev-0.8B (open Jev-style model)",
    "jev-kev4b": "jev-lean harness, Kev-4B (open Jev-style model)",
    "jev-von": "jev-lean harness, Von 1.2 (open Jev-style model)",
    "jev-typesafe": "jev-lean harness, **Jev itself** (TypeSafe API, jev-1.13.0)",
    "waterfall": "`waterfall` (default search, effort 1000)",
}


def load(label: str, context: str) -> dict[str, dict]:
    path = ROOT / "results" / f"{label}.{context}.jsonl"
    if not path.exists():
        return {}
    rows = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    return {row["id"]: row for row in rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--context", choices=["student", "solutions"], required=True)
    args = parser.parse_args()
    tasks = {t["id"]: t for t in json.loads((ROOT / "tasks.json").read_text()) if t["context"] == args.context}
    base = load("sorry", args.context)
    arms = {label: load(label, args.context) for label in ORDER}
    arms = {k: v for k, v in arms.items() if v}
    volumes = sorted({t["volume"] for t in tasks.values()})

    print(f"### {args.context} context: {len(tasks)} tasks\n")
    print("| Arm | Strict | Lenient | " + " | ".join(f"{v} strict" for v in volumes) + " | Median tactic s | Timeouts |")
    print("| --- | ---: | ---: | " + " | ".join("---:" for _ in volumes) + " | ---: | ---: |")
    for label, rows in arms.items():
        strict = sum(r["strict"] for r in rows.values())
        lenient = sum(r["lenient"] for r in rows.values())
        per_volume = [sum(r["strict"] for i, r in rows.items() if tasks[i]["volume"] == v) for v in volumes]
        deltas = [max(0.0, r["seconds"] - base[i]["seconds"]) for i, r in rows.items() if i in base]
        timeouts = sum(r["status"] == "timeout" for r in rows.values())
        missing = len(tasks) - len(rows)
        note = f" ({missing} not run)" if missing else ""
        print(f"| {LABELS[label]}{note} | {strict} ({100 * strict / len(tasks):.0f}%) | {lenient} | "
              + " | ".join(str(n) for n in per_volume)
              + f" | {statistics.median(deltas):.2f} | {timeouts} |" if deltas else " | n/a | {timeouts} |")
    print("\nVolume sizes: " + ", ".join(f"{v} {sum(t['volume'] == v for t in tasks.values())}" for v in volumes))

    if "waterfall" in arms:
        wf = {i for i, r in arms["waterfall"].items() if r["strict"]}
        print("\n| Other arm | Both | Only waterfall | Only other | Union |")
        print("| --- | ---: | ---: | ---: | ---: |")
        for label, rows in arms.items():
            if label == "waterfall":
                continue
            other = {i for i, r in rows.items() if r["strict"]}
            print(f"| {label} | {len(wf & other)} | {len(wf - other)} | {len(other - wf)} | {len(wf | other)} |")

    jev_arms = [label for label in arms if label.startswith("jev-")]
    if len(jev_arms) > 1:
        common = [i for i in tasks if all(arms[a].get(i, {}).get("strict") for a in jev_arms)]
        ranked = [i for i in common if all(arms[a][i]["jev"]["metrics"]["jev_calls"] > 0 for a in jev_arms)]
        if ranked:
            print(f"\nSearch effort on the {len(ranked)} tasks that every jev-lean arm proves and where "
                  "the search consulted the ranker (fewer attempted transitions means better ranking):\n")
            print("| Arm | Mean attempted transitions | Median |")
            print("| --- | ---: | ---: |")
            for a in jev_arms:
                t = [arms[a][i]["jev"]["metrics"]["attempted_transitions"] for i in ranked]
                print(f"| {a} | {statistics.mean(t):.1f} | {statistics.median(t):g} |")

    status = {label: Counter(r["status"] for r in rows.values()) for label, rows in arms.items()}
    print("\nStatus counts: " + "; ".join(f"{k} {dict(v)}" for k, v in status.items()))
    for label in ("jev-llm", "jev-llm7b", "jev-kev", "jev-kev4b", "jev-von", "jev-typesafe"):
        stats = ROOT / "results" / f"broker-{label}.{args.context}.json"
        if not (stats.exists() and label in arms):
            continue
        data = json.loads(stats.read_text())
        calls = [r["jev"]["metrics"]["jev_calls"] for r in arms[label].values() if r.get("jev")]
        print(f"\n{label}: {data['calls']} calls, "
              f"{data['seconds'] / max(data['calls'], 1):.2f} s per call, "
              f"{data['prompt_tokens'] / max(data['calls'], 1):.0f} uncached prompt tokens per call, "
              f"{statistics.mean(calls) if calls else 0:.1f} ranking calls per task.")

if __name__ == "__main__":
    main()

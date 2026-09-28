"""Where does waterfall spend its attempts?  Reads results/capture/<context>/*.json
written by the `wf-capture` arm (bench/WfCapture.lean).

For each run it splits the attempted actions three ways:
  * closers (group `close`): leaf solvers tried at a node;
  * structural moves that succeeded locally (produced children);
  * structural moves that failed.
For successful proofs it also separates attempts spent in earlier depth/strength
trials from those in the final, successful trial, and compares the latter with
the length of the proof: the excess is what a perfect ranker could save.
"""
from __future__ import annotations

import argparse
import glob
import json
import statistics
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load(context: str) -> list[dict]:
    runs = []
    for path in glob.glob(str(ROOT / "results" / "capture" / context / "*.json")):
        with open(path) as handle:
            runs.append(json.load(handle))
    return runs


def trial_of(rows: dict, row_id: int | None) -> int | None:
    while row_id is not None and row_id in rows:
        if rows[row_id]["phase"] == "trial":
            return row_id
        row_id = rows[row_id]["parent"]
    return None


def summarize(runs: list[dict], title: str) -> None:
    print(f"## {title}: {len(runs)} runs\n")
    groups = Counter()
    ok_by_group = Counter()
    for run in runs:
        for action in run["actions"]:
            groups[action["group"]] += 1
            ok_by_group[action["group"]] += action["ok"]
    total = sum(groups.values())
    print("| Group | Attempts | Share | Local success rate |")
    print("| --- | ---: | ---: | ---: |")
    for group, n in groups.most_common():
        print(f"| {group} | {n} | {100 * n / total:.0f}% | {100 * ok_by_group[group] / n:.0f}% |")

    # Closers are tried in order at each node until one closes the goal.
    node_closers = defaultdict(list)
    for index, run in enumerate(runs):
        for action in run["actions"]:
            if action["group"] == "close":
                node_closers[(index, action["parent"])].append(action["ok"])
    dead = [v for v in node_closers.values() if not any(v)]
    wasted = sum(len(v) for v in dead)
    closer_total = sum(len(v) for v in node_closers.values())
    before_hit = sum(v.index(True) for v in node_closers.values() if any(v))
    print(f"\nCloser attempts: {closer_total}, at {len(node_closers)} nodes. "
          f"At {len(dead)} nodes ({100 * len(dead) / max(len(node_closers), 1):.0f}%) no closer succeeded; "
          f"those account for {wasted} attempts ({100 * wasted / max(total, 1):.0f}% of all attempts). "
          f"Where a closer did succeed, {before_hit} failed closers were tried first.\n")


def successes(runs: list[dict]) -> None:
    solved = [r for r in runs if r["success"]]
    rows_needed = []
    earlier = within = steps_total = 0
    ratios = []
    for run in solved:
        rows = {r["id"]: r for r in run["rows"]}
        trials = [r["id"] for r in run["rows"] if r["phase"] == "trial"]
        final = trials[-1] if trials else None
        in_final = [a for a in run["actions"] if trial_of(rows, a["parent"]) == final]
        steps = len(run["steps"])
        earlier += len(run["actions"]) - len(in_final)
        within += len(in_final) - steps
        steps_total += steps
        if steps:
            ratios.append(len(in_final) / steps)
        rows_needed.append(len(run["actions"]))
    n = max(len(solved), 1)
    print(f"## Successful proofs: {len(solved)}\n")
    print(f"Median attempts per proof: {statistics.median(rows_needed) if rows_needed else 0}; "
          f"mean proof length {steps_total / n:.1f} steps.")
    print(f"Attempts in earlier depth/strength trials: {earlier} ({earlier / n:.1f} per proof).")
    print(f"Attempts in the successful trial beyond the proof's own steps: {within} "
          f"({within / n:.1f} per proof). A ranker that always chose the proof's step first "
          f"would save at most these.")
    big = sorted(ratios)
    if big:
        print(f"Final-trial attempts per proof step: median {statistics.median(big):.1f}, "
              f"90th percentile {big[int(0.9 * len(big))]:.1f}.\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--context", default="solutions")
    args = parser.parse_args()
    runs = load(args.context)
    summarize([r for r in runs if not r["success"]], "Failed searches")
    summarize([r for r in runs if r["success"]], "Successful searches")
    successes(runs)


if __name__ == "__main__":
    main()

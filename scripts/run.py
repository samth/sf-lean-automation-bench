"""Run one tactic arm over the extracted sf-in-lean tasks.

Each task becomes a file: the chapter prefix, the target statement, and
``:= by <tactic>``, followed by ``#print axioms``.  A task counts as

* ``lenient`` when the target elaborates without error, even if its proof
  cites admitted exercises, and
* ``strict`` when it is also free of ``sorryAx``.

Results are appended to ``results/<arm>.<context>.jsonl``; reruns skip ids
that already have a row.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

ARMS: dict[str, dict] = {
    "sorry": {"imports": [], "tactic": "sorry"},
    "auto": {"imports": ["SFBench"], "tactic": "sf_auto"},
    "induct": {"imports": ["SFBench"], "tactic": "sf_induct"},
    "aesop": {"imports": ["Aesop"], "tactic": "aesop"},
    "waterfall": {"imports": ["waterfall"], "tactic": "waterfall"},
    # Higher-effort Waterfall, with Lean's heartbeat limit scaled to match (default 200000).
    # Oracle premise selection: the SF lemmas that the reference proof cites,
    # read per task from the JSON file named by ORACLE_RULES.
    "waterfall-oracle": {"imports": ["waterfall"], "tactic": "waterfall", "oracle": True},
    "waterfall-rules": {"imports": ["waterfall"], "tactic": "waterfall", "oracle": True},
    "waterfall-e4000": {"imports": ["waterfall"],
                        "tactic": "set_option maxHeartbeats 800000 in waterfall (effort := 4000)"},
    "waterfall-e16000": {"imports": ["waterfall"],
                         "tactic": "set_option maxHeartbeats 3200000 in waterfall (effort := 16000)"},
    "jev": {"imports": ["JevLean"], "tactic": "jev_benchmark?"},
    # Experiment: waterfall with its attempts recorded (results/capture/<context>/).
    "wf-capture": {"imports": ["WfCapture"], "tactic": "wf_capture"},
}

AXIOMS_RE = re.compile(r"'(?P<name>.+?)' (?:depends on axioms: \[(?P<axioms>[^\]]*)\]|does not depend on any axioms)")


def task_source(task: dict, arm: dict) -> tuple[str, int]:
    """Return the task file text and the 1-based line where the target starts."""
    prefix = task["prefix"]
    lines = prefix.split("\n")
    header = lines[:60]
    is_module = any(line.strip() == "module" for line in header)
    last_import = max((i for i, line in enumerate(header) if re.match(r"(public |meta |private )*import ", line)),
                      default=-1)
    if last_import < 0 and is_module:
        last_import = next(i for i, line in enumerate(header) if line.strip() == "module")
    # A module file (Lean's module system) can import only modules, and publicly.
    keyword = "public import" if is_module else "import"
    tool_imports = [f"{keyword} {module}" for module in arm["imports"]]
    lines[last_import + 1:last_import + 1] = tool_imports
    prefix = "\n".join(lines)
    target_line = prefix.count("\n") + 1
    tactic = arm["tactic"]
    if arm.get("oracle"):
        rules = json.loads(Path(os.environ["ORACLE_RULES"]).read_text()).get(task["id"], [])
        tactic = f"{tactic} [{', '.join(rules)}]" if rules else tactic
    body = f"{task['header']}\n:= by\n  {tactic}\n\n#print axioms {task['name']}\n"
    return prefix + body, target_line


def run_task(task: dict, arm_name: str, arm: dict, timeout: float, env: dict) -> dict:
    workspace = ROOT / "bench" / f"ctx-{task['context']}"
    source, target_line = task_source(task, arm)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=workspace / "Tasks", delete=False) as handle:
        handle.write(source)
        path = Path(handle.name)
    started = time.monotonic()
    row = {"id": task["id"], "arm": arm_name}
    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--json", str(path.relative_to(workspace))],
            cwd=workspace, capture_output=True, text=True, timeout=timeout, env=env,
        )
        row["seconds"] = round(time.monotonic() - started, 3)
        messages = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
        context_errors = [m for m in messages if m["severity"] == "error" and m["pos"]["line"] < target_line]
        target_errors = [m for m in messages if m["severity"] == "error" and m["pos"]["line"] >= target_line]
        axioms = None
        for message in messages:
            match = AXIOMS_RE.search(message.get("data", ""))
            if match and message["pos"]["line"] >= target_line:
                axioms = [a.strip() for a in (match.group("axioms") or "").split(",") if a.strip()]
        for message in messages:
            data = message.get("data", "")
            if "WFCAPTURE " in data:
                capture_dir = ROOT / "results" / "capture" / task["context"]
                capture_dir.mkdir(parents=True, exist_ok=True)
                name = re.sub(r"[^A-Za-z0-9_.-]", "_", task["id"]) + ".json"
                (capture_dir / name).write_text(data.split("WFCAPTURE ", 1)[1])
        jev = None
        for message in messages:
            data = message.get("data", "")
            if "JEVLEAN_BENCHMARK_RESULT " in data:
                jev = json.loads(data.split("JEVLEAN_BENCHMARK_RESULT ", 1)[1])
        lenient = not target_errors and axioms is not None and arm_name != "sorry"
        row.update({
            "status": "context_error" if context_errors else ("solved" if lenient else "failed"),
            "lenient": lenient and not context_errors,
            "strict": lenient and not context_errors and "sorryAx" not in axioms,
            "axioms": axioms,
            "error": (target_errors or context_errors or [{}])[0].get("data", "")[:400] or None,
        })
        if jev:
            row["jev"] = {"metrics": jev.get("metrics"), "proof": jev.get("proof")}
    except subprocess.TimeoutExpired:
        row.update({"seconds": round(time.monotonic() - started, 3), "status": "timeout",
                    "lenient": False, "strict": False})
    finally:
        path.unlink(missing_ok=True)
    return row


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arm", required=True, choices=sorted(ARMS))
    parser.add_argument("--label", help="result label (default: arm name)")
    parser.add_argument("--context", choices=["student", "solutions"], required=True)
    parser.add_argument("--filter", default="", help="regex over task ids")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--ids-file", help="run only the task ids listed in this file, one per line")
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--broker-port", type=int, help="JEV_MODEL_BROKER_PORT for the jev arm")
    args = parser.parse_args()

    label = args.label or args.arm
    tasks = [t for t in json.loads((ROOT / "tasks.json").read_text())
             if t["context"] == args.context and re.search(args.filter, t["id"])]
    if args.ids_file:
        wanted = {line.strip() for line in open(args.ids_file) if line.strip()}
        tasks = [t for t in tasks if t["id"] in wanted]
    out = ROOT / "results" / f"{label}.{args.context}.jsonl"
    out.parent.mkdir(exist_ok=True)
    done = set()
    if out.exists():
        done = {json.loads(line)["id"] for line in out.read_text().splitlines() if line.strip()}
    tasks = [t for t in tasks if t["id"] not in done][: args.limit]
    (ROOT / "bench" / f"ctx-{args.context}" / "Tasks").mkdir(exist_ok=True)
    env = dict(os.environ)
    env.pop("TYPESAFE_API_KEY", None)
    if args.broker_port:
        env["JEV_MODEL_BROKER_PORT"] = str(args.broker_port)
    arm = ARMS[args.arm]
    solved = total = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as pool, out.open("a") as sink:
        futures = [pool.submit(run_task, t, label, arm, args.timeout, env) for t in tasks]
        for future in as_completed(futures):
            row = future.result()
            if "oversize request" in (row.get("error") or ""):
                row["status"] = "ranker_oversize"   # the broker refused an input over its size limit
            elif "rank broker" in (row.get("error") or ""):
                # The ranker failed (e.g. its server died); leave the task for a resume.
                print(f"{label}/{args.context}: ranker failed on {row['id']}; not recorded", flush=True)
                continue
            sink.write(json.dumps(row, ensure_ascii=False) + "\n")
            sink.flush()
            total += 1
            solved += row["strict"]
            if total % 50 == 0:
                print(f"{label}/{args.context}: {total}/{len(tasks)} done, {solved} strict", flush=True)
    print(f"{label}/{args.context}: finished {total} tasks, {solved} strict")


if __name__ == "__main__":
    main()

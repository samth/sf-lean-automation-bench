"""Build sf-in-lean benchmark contexts and extract theorem tasks.

Two contexts mirror the two readings of Koppel's comparison:

* ``student``: the student variant, whose exercise proofs stay admitted.
  Exercise *definitions* are taken from the solutions variant so that their
  test theorems are provable at all.  Tasks are the elided exercise theorems.
* ``solutions``: the solutions variant, where every earlier result is proved.
  Tasks are every theorem and example in the three volumes.

Each task is a chapter prefix that ends with the target declaration; its proof
is the placeholder ``__PROOF__``, which the runner replaces with a tactic.
"""
from __future__ import annotations

import argparse
import os
import json
import re
import shutil
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SFL_OUT = Path(os.environ.get("SFL_OUT", ROOT / "vendor/sf-in-lean/_out"))
VOLUMES = ("lf", "hl", "ts")

DECL_RE = re.compile(
    r"^(?P<mods>(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial)\s+)*)"
    r"(?P<kind>theorem|lemma|example|def|abbrev|instance)\b\s*(?P<name>[^\s:({\[⦃]*)"
)


def chapter_files(variant: str) -> dict[str, Path]:
    """Map module path (e.g. ``LF/Basics.lean``) to its file, merging volumes."""
    files: dict[str, Path] = {}
    for volume in VOLUMES:
        base = SFL_OUT / volume / variant / "lean"
        for path in sorted(base.glob("[A-Z][A-Z]/*.lean")):
            rel = path.relative_to(base).as_posix()
            if rel.split("/")[0].lower() != volume and rel in files:
                continue
            if rel.split("/")[0].lower() == volume or rel not in files:
                files[rel] = path
    return files


def blocks(lines: list[str]) -> list[dict]:
    """Split a file into top-level declarations at column 0."""
    starts = []
    for index, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match:
            starts.append((index, match))
    result = []
    for position, (start, match) in enumerate(starts):
        end = start + 1
        while end < len(lines):
            line = lines[end]
            if line and not line[0].isspace() and not line.startswith(("|", ")", "}", "]")):
                break
            end += 1
        while end > start + 1 and not lines[end - 1].strip():
            end -= 1
        result.append({
            "start": start, "end": end, "kind": match.group("kind"),
            "name": match.group("name"), "text": "\n".join(lines[start:end]),
        })
    return result


def code_part(text: str) -> str:
    """Drop line comments and block comments so ``sorry`` in prose is ignored."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return "\n".join(line.split("--")[0] for line in text.split("\n"))


def proof_start(text: str) -> int | None:
    """Offset of the proof ``:=`` at bracket depth zero, or of equation arms."""
    depth = 0
    stripped = code_part(text)
    for index, char in enumerate(stripped):
        if char in "([{⟨⦃":
            depth += 1
        elif char in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and stripped.startswith(":=", index):
            return index
    match = re.search(r"\n\s*\|", stripped)
    return match.start() if match else None


def build_context(variant: str, patch_defs: bool) -> dict[str, list[str]]:
    """Copy one variant into ``bench/ctx-<name>`` and return patched chapter lines."""
    files = chapter_files(variant)
    solutions = chapter_files("solutions")
    chapters: dict[str, list[str]] = {}
    for rel, path in files.items():
        lines = path.read_text().split("\n")
        if patch_defs:
            sol_blocks = {
                b["name"]: b for b in blocks(solutions[rel].read_text().split("\n"))
                if b["kind"] in ("def", "abbrev", "instance") and b["name"]
            }
            for block in reversed(blocks(lines)):
                if block["kind"] in ("def", "abbrev", "instance") and re.search(
                    r"\bsorry\b", code_part(block["text"])
                ) and block["name"] in sol_blocks and "sdcom" not in sol_blocks[block["name"]]["text"]:
                    lines[block["start"]:block["end"]] = sol_blocks[block["name"]]["text"].split("\n")
        chapters[rel] = lines
    return chapters


def write_workspace(name: str, chapters: dict[str, list[str]]) -> Path:
    workspace = ROOT / "bench" / f"ctx-{name}"
    for sub in ("LF", "HL", "TS", "SFLCompat", "Tasks"):
        shutil.rmtree(workspace / sub, ignore_errors=True)
    workspace.mkdir(parents=True, exist_ok=True)
    shutil.copytree(SFL_OUT / "lf/student/lean/SFLCompat", workspace / "SFLCompat")
    shutil.copy(SFL_OUT / "lf/student/lean/SFLCompat.lean", workspace / "SFLCompat.lean")
    for rel, lines in chapters.items():
        target = workspace / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("\n".join(lines))
    template = (ROOT / "bench/lakefile.template.toml").read_text()
    (workspace / "lakefile.toml").write_text(template.replace("@NAME@", name))
    (workspace / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc2\n")
    for name in ("SFBench.lean", "Positions.lean"):
        shutil.copy(ROOT / "bench" / name, workspace / name)
    shutil.copy(ROOT / "bench/JevLean/JevLean.lean", workspace / "JevLean.lean")
    return workspace


def positions(workspace: Path, rel: str) -> list[dict]:
    """Ask Lean for the exact proof offsets of every theorem and example."""
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "Positions.lean", rel],
        cwd=workspace, capture_output=True, text=True, timeout=900,
    )
    errors = [line for line in result.stderr.splitlines() if "error" in line]
    if result.returncode != 0 or errors:
        raise RuntimeError(f"{rel}: {result.stderr[-2000:]}")
    return [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]


def extract(context: str, workspace: Path, chapters: dict[str, list[str]]) -> list[dict]:
    rels = sorted(chapters)
    with ThreadPoolExecutor(max_workers=12) as pool:
        found = dict(zip(rels, pool.map(lambda rel: positions(workspace, rel), rels)))
    tasks = []
    for rel in rels:
        data = (workspace / rel).read_bytes()
        chapter = rel.removesuffix(".lean").replace("/", ".")
        example_index = 0
        for decl in found[rel]:
            header = data[decl["start"]:decl["proof"]].decode().rstrip()
            proof = data[decl["proof"]:decl["end"]].decode()
            if decl["kind"] == "example":
                example_index += 1
                name = f"sf_example_{example_index}"
                header = re.sub(r"\bexample\b", f"theorem {name}", header, count=1)
            else:
                name = decl["name"]
            if context == "student" and not re.search(r"\bsorry\b", code_part(proof)):
                continue
            prefix = data[:decl["start"]].decode()
            line = prefix.count("\n") + 1
            tasks.append({
                "id": f"{context}:{chapter}:{name}:{line}",
                "context": context, "volume": rel.split("/")[0], "chapter": chapter,
                "name": name, "kind": decl["kind"], "line": line,
                "prefix": prefix, "header": header, "reference": proof,
            })
    return tasks


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    student = build_context("student", patch_defs=True)
    solutions = build_context("solutions", patch_defs=False)
    all_tasks = []
    for name, chapters in (("student", student), ("solutions", solutions)):
        workspace = write_workspace(name, chapters)
        print(f"building ctx-{name} (first run downloads and builds dependencies)", flush=True)
        subprocess.run(["lake", "build"], cwd=workspace, check=True)
        subprocess.run(["lake", "build", "waterfall", "Aesop"], cwd=workspace, check=True)
        tasks = extract(name, workspace, chapters)
        all_tasks += tasks
        print(f"{name}: {len(tasks)} tasks")
    out = ROOT / "tasks.json"
    out.write_text(json.dumps(all_tasks, ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main()

# Proof automation on Software Foundations in Lean

This repository compares automatic provers on the exercises of
[Software Foundations in Lean](https://github.com/plclub/sf-in-lean), PLClub's
port of *Logical Foundations*, *Hoare Logic* and *Type Systems*. Three kinds
of tool take part: [`waterfall`](https://github.com/samth/waterfall), the
jev-lean search harness built for TypeSafe's Jev model, and standard Lean
automation. Everything runs locally.

It began as an attempt to approximate a comparison that Jimmy Koppel
[posted](https://x.com/jimmykoppel/status/2103308940947960203) in September
2026. His code is private, so this is an independent reconstruction: the task
set, harness and scoring here are ours, and the numbers are not his.

**No run here uses Jev itself.** Jev is TypeSafe's hosted model. The `jev-*`
arms run the public [jev-lean](https://github.com/jesyspa/jev-lean) search
harness, the Lean tactic built to call Jev. In place of Jev they use open
Jev-style decision models served locally through the same API, plus ablations
with no model; see [Arms](#arms).

## Results

Strict successes, measured on one Ubuntu machine on 2026-09-26 and 27. Every
number comes from `results/*.jsonl`; [RESULTS.md](RESULTS.md) has per-volume
counts, timings, overlaps and ranking effort.

| Arm | Exercises (590) | All theorems (1,448) |
| --- | ---: | ---: |
| `waterfall` | **386 (65%)** | **1,088 (75%)** |
| jev-lean + Kev-0.8B | 246 (42%) | not run |
| jev-lean + Von 1.2 | 239 (41%) | 796 of 1,377 run |
| jev-lean, no model | 247 (42%) | 805 (56%) |
| jev-lean, hand-written ranking | 240 (41%) | 804 (56%) |
| jev-lean + prompted Qwen2.5-Coder-1.5B | 240 (41%) | not run |
| every single induction or case split | 245 (42%) | 748 (52%) |
| automation only | 219 (37%) | 699 (48%) |
| `aesop` | 196 (33%) | 660 (46%) |

* **Waterfall proves the most.** On the exercises, it proves every task that
  any other arm proves. On all theorems, the other arms together add 10 tasks
  to its 1,088.
* **Within jev-lean, the ranker hardly changes coverage.** With no model the
  harness proves 247 exercises; with Kev, 246. Its fixed candidate list and
  budget, not the order of candidates, bound what it can prove.
* **Kev ranks best.** On the 32 exercises that every jev-lean arm proves after
  consulting its ranker, Kev reaches a proof in 42 attempted transitions on
  average, against 55 with no model. Von and the prompted code model do no
  better than catalogue order.
* **Koppel reported Waterfall at 27% and Jev at 39%.** Here Waterfall proves
  65% of the exercises, and the jev-lean harness 40 to 42% with any ranker.
  His task list and harness are not public, so the 27% cannot be traced.

Von's run on all theorems stopped after 1,377 of the 1,448 tasks when the
machine ran short of memory, and Kev has not been run on that set;
`scripts/run_all.sh solutions --arms "jev-von jev-kev"` resumes both. The
prompted Qwen arm was run only on the exercises.

## Tasks

`setup.sh` builds sf-in-lean at a pinned commit and extracts two task sets.

* **Exercises** (`student` context, 590 tasks). Every theorem or example whose
  proof the student edition elides. Other exercises stay admitted, as a student
  would see them. Exercise *definitions*, such as `nand`, come from the
  solutions edition; otherwise their tests would be unprovable. A few
  decorated-program definitions in Hoare2 cannot be patched in and stay
  admitted.
* **All theorems** (`solutions` context, 1,448 tasks). Every theorem and example
  in the solutions edition, with every earlier result proved.

Each task is the chapter truncated after the target declaration, with the
proof replaced by `by <tactic>`. Lean itself reports where each proof starts,
so statements that contain `:=`, like Imp assignments, split correctly. A task
succeeds **strictly** when the proof checks and `#print axioms` shows no
`sorryAx`. It succeeds **leniently** when it checks but cites an admitted
exercise.

## Arms

| Arm | What runs |
| --- | --- |
| `auto` | `first \| rfl \| simp_all \| grind \| omega \| decide`, no induction |
| `induct` | `auto`, then each single `induction` or `cases` on a local followed by `auto` on every goal |
| `aesop` | `aesop` with default settings, the closest Lean analogue of Rocq's `eauto` |
| `waterfall` | `waterfall` 0.2.0 with default settings (search mode, effort 1000) |
| `jev-stable` | jev-lean's `jev?` search, candidates tried in catalogue order (no model) |
| `jev-heuristic` | the same search, candidates ordered by hand-written preferences |
| `jev-kev` | the same search, ranked by [Kev-0.8B](https://github.com/jaredpalmer/kev), an open Jev replica |
| `jev-von` | the same search, ranked by [Von 1.2](https://github.com/wfzyx/von), an open non-autoregressive decision model |
| `jev-llm` | the same search, ranked by a prompted Qwen2.5-Coder-1.5B (a general code model, not Jev-like) |

The jev-lean harness asks a localhost broker to rank a list of Lean-checked
candidate tactics, then searches in that order. `broker/local_broker.py`
speaks the same protocol as jev-lean's TypeSafe broker.

* For `jev-kev` and `jev-von`, the broker sends jev-lean's own Jev request,
  one `choice` question whose options are the candidate tactics, to a local
  server implementing TypeSafe's `POST /v1/systemone` API. It then parses the
  probabilities exactly as jev-lean does. Kev takes the request unchanged. Von
  accepts only string option descriptions, so each option is sent as the bare
  tactic text. Kev (Jared Palmer) fine-tunes Qwen3.5 with a decision head and
  reports accuracy within a few points of Jev on held-out sources. Von is a
  395M ModernBERT encoder whose option scores do not depend on option order.
  Both run on the CPU here.
* For `jev-llm`, the broker gives each candidate a one-character label and
  reads the label probabilities from one forward pass of a code model served by
  llama.cpp. This was a first approximation, kept for comparison.

`bench/JevLean` vendors jev-lean with a small port to Lean v4.34.0-rc2,
described in its header. The search keeps jev-lean's default
budgets: 256 attempted transitions, 64 nodes and 16 ranking calls per goal.
Only the wall-clock limit changes. It rises from 10 s to 60 s for the
catalogue-order, heuristic and prompted-LLM arms, and to 600 s for Kev and Von.
A hosted Jev answers in milliseconds, so the clock should never be what stops
its search.

## Running it

Tested on Ubuntu x86-64. Requirements: `elan`, `git`, `make`, `python3` 3.10
or newer, `curl` and `sha256sum`. `--jev-like` also needs
[uv](https://docs.astral.sh/uv/); Kev and Von fetch their weights from Hugging
Face on first use. `--llm` downloads the Linux x86-64 CPU build of llama.cpp
and two GGUF models (6.6 GB).

```sh
./setup.sh --jev-like             # add --llm for the prompted-LLM arms
scripts/run_all.sh student        # default arms on the exercises
scripts/run_all.sh solutions --arms "auto waterfall jev-stable"
python3 scripts/score.py --context student
```

Runs append to `results/<arm>.<context>.jsonl` and skip tasks already
recorded, so an interrupted run resumes. Delete a file to rerun its arm.

To rank with Jev itself, set a TypeSafe key and run the `jev-typesafe` arm.
It sends the same request as the Kev and Von arms to TypeSafe's API, and
TypeSafe bills the calls:

```sh
TYPESAFE_API_KEY=... scripts/run_all.sh student --arms jev-typesafe
```

## Caveats

* The jev-lean harness is a design similar to Koppel's Rocq harness, but it is
  not his harness, and a small local model is not Jev.
* Times are wall-clock on one machine that often ran several arms at once, so
  treat them as rough. RESULTS.md reports tactic time: task time minus the
  time to elaborate the same file with `sorry`.
* Several arms first ran from an earlier local copy of this code. Rerunning
  the deterministic arms from this repository reproduced every outcome. The
  Kev, Von and Qwen results come from the earlier copy of the same broker and
  jev-lean port. Converting SFBench and JevLean to Lean modules, needed for the
  one module chapter (LF/CustomTactics), changed no outcome on either task
  set.
* Some basic exercises defeat every arm, including Waterfall. One example is
  `zero_mul` on LF/Induction's custom `Nat`, which Waterfall misses even when
  the definitions are passed in brackets. This benchmark does not diagnose why.
* Waterfall and the baselines use Lean's default `maxHeartbeats`. Every task
  also has a process limit, 120 s or 900 s for the model arms; see the
  Timeouts column.
* Kev and Von were run on a CPU. Their per-call latency here says nothing
  about their speed on a GPU, and nothing about Jev's.

## License

Apache License 2.0. `bench/JevLean` is adapted from jev-lean, also Apache 2.0;
its header lists the changes. sf-in-lean, Kev, Von, llama.cpp and the models
are fetched by `setup.sh` under their own licenses and are not redistributed
here.

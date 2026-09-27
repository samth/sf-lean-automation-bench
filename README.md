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

The `jev-*` arms run the public [jev-lean](https://github.com/jesyspa/jev-lean)
search harness, the Lean tactic built to call TypeSafe's Jev model. One arm
ranks with Jev itself through TypeSafe's API. The others rank with open
Jev-style models served locally through the same API, or with no model at
all; see [Arms](#arms).

## Results

Strict successes, measured on one Ubuntu machine from 2026-09-26 to 28. Every
number comes from `results/*.jsonl`; [RESULTS.md](RESULTS.md) has per-volume
counts, timings, overlaps and ranking effort.

| Arm | Exercises (590) | All theorems (1,448) |
| --- | ---: | ---: |
| `waterfall` | **386 (65%)** | **1,088 (75%)** |
| jev-lean + Jev (TypeSafe API) | 247 (42%) | 823 (57%) |
| jev-lean + Kev-0.8B | 246 (42%) | 814 (56%) |
| jev-lean + Von 1.2 | 239 (41%) | 801 (55%) |
| jev-lean, no model | 247 (42%) | 805 (56%) |
| jev-lean, hand-written ranking | 240 (41%) | 804 (56%) |
| jev-lean + prompted Qwen2.5-Coder-1.5B | 240 (41%) | not run |
| every single induction or case split | 245 (42%) | 748 (52%) |
| automation only | 219 (37%) | 699 (48%) |
| `aesop` | 196 (33%) | 660 (46%) |

* **Waterfall proves the most.** On the exercises, it proves every task that
  any other arm proves, Jev included. On all theorems, the other arms together
  add 13 tasks to its 1,088.
* **Jev barely changes what jev-lean can prove.** With Jev the harness proves
  247 exercises, the same number as with no model at all; the two differ on 6
  tasks each way. On all theorems Jev gains 18: 823 against 805. The harness's
  fixed candidate list and budget, not the order of candidates, bound what it
  can prove.
* **Jev and Kev rank best.** On the 103 theorems that every jev-lean arm proves
  after consulting its ranker, Jev reaches a proof in 36 attempted transitions
  on average, Kev-0.8B in 38, and the harness with no model in 46. On the 32
  such exercises the figures are 42, 42 and 55. Von, the hand-written ranking
  and the prompted code model do no better than catalogue order.
* **Koppel reported Jev at 39% and Waterfall at 27%.** Here Jev in the jev-lean
  harness proves 42% of the exercises, close to his figure. Waterfall proves
  65%. His task list and harness are not public, so his 27% cannot be traced.

The prompted Qwen arm was run only on the exercises. Jev's run used about 10.3
million input tokens over 10,800 ranking calls, at 0.14 s per call.

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
| `jev-typesafe` | the same search, ranked by Jev itself through TypeSafe's API (model `jev-1.13.0`) |
| `jev-kev` | the same search, ranked by [Kev-0.8B](https://github.com/jaredpalmer/kev), an open Jev replica |
| `jev-von` | the same search, ranked by [Von 1.2](https://github.com/wfzyx/von), an open non-autoregressive decision model |
| `jev-llm` | the same search, ranked by a prompted Qwen2.5-Coder-1.5B (a general code model, not Jev-like) |

The jev-lean harness asks a localhost broker to rank a list of Lean-checked
candidate tactics, then searches in that order. `broker/local_broker.py`
speaks the same protocol as jev-lean's TypeSafe broker.

* For `jev-typesafe`, `jev-kev` and `jev-von`, the broker sends jev-lean's
  own Jev request, one `choice` question whose options are the candidate
  tactics, to a server implementing TypeSafe's `POST /v1/systemone` API:
  TypeSafe's own, or a local one. It parses the probabilities as jev-lean
  does, with one change. Jev rounds each probability to two decimals, and with
  many options the rounded values can miss jev-lean's check that they sum to
  within 0.01 of 1. The broker allows the rounding bound, 0.005 per option.
  Kev and Jev take the request unchanged. Von
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
Only the wall-clock limit changes. It rises from 10 s to 60 s for the Jev,
catalogue-order, heuristic and prompted-LLM arms, and to 600 s for Kev and Von,
which run on a CPU here. The clock should never be what stops a search.

If a ranking call fails, the task is not recorded, so a resumed run retries it
rather than silently searching in catalogue order.

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

On a CPU, a Kev server's memory grows with the length of the goals it ranks.
`scripts/run_capped.sh` wraps `run_all.sh`, restarting it if the model servers
exceed a memory cap or die, and gives up after three restarts with no new
result. `run_all.sh` also runs each model server under a hard cgroup memory
limit (`MODEL_MEMORY_MAX`, default 10G) where `systemd-run --user` works, and
`MODEL_MAX_REQUEST_BYTES` makes the broker refuse larger requests, which are
recorded as `ranker_oversize`. The Kev run on all theorems finished with:

```sh
OMP_NUM_THREADS=4 MODEL_MEMORY_MAX=10G MODEL_MAX_REQUEST_BYTES=20000 KEV_ATTN=sdpa \
  nice -n 19 taskset -c 14-19 scripts/run_capped.sh 11 solutions --arms jev-kev --model-jobs 1
```

## Caveats

* The jev-lean harness is a design similar to Koppel's Rocq harness, but it is
  not his harness.
* Jev's answers vary between identical calls, so a rerun of the Jev arm can
  differ by a few tasks.
* Kev's last 209 theorems on the all-theorems set, all in the Type Systems
  volume, ran with PyTorch's memory-efficient attention (`KEV_ATTN=sdpa`)
  instead of Kev's CPU default, and with requests over 20 KB refused. The two
  compute the same attention up to floating-point rounding. Three of those
  tasks were refused as too large for this machine, and count as unproved.
* Von reads at most 8,192 tokens. A few Type Systems goals are longer; Von
  warns and answers anyway, so its rankings on them may be degraded.
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

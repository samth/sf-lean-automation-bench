# Proof automation on Software Foundations in Lean

This repository compares automatic provers on the exercises of
[Software Foundations in Lean](https://github.com/plclub/sf-in-lean), PLClub's
port of *Logical Foundations*, *Hoare Logic* and *Type Systems*. Three kinds
of tool take part: [`waterfall`](https://github.com/samth/waterfall), the
jev-lean search harness built for TypeSafe's Jev model, and standard Lean
automation. Everything but Jev runs locally.

It began as an attempt to approximate a comparison that Jimmy Koppel
[posted](https://x.com/jimmykoppel/status/2103308940947960203) in September
2026. His code is private, so this is an independent reconstruction: the task
set, harness and scoring here are ours, and the numbers are not his.

The `jev-*` arms run the public [jev-lean](https://github.com/jesyspa/jev-lean)
search harness, the Lean tactic built to call TypeSafe's Jev model, ranked by
Jev itself or by no model at all. Runs with open Jev-style models in Jev's
place, such as Kev and Von, are described in
[docs/open-jev-models.md](docs/open-jev-models.md).

## Results

Strict successes, measured on one Ubuntu machine from 2026-09-26 to 28. Every
number comes from `results/*.jsonl`; [RESULTS.md](RESULTS.md) has per-volume
counts, timings, overlaps and ranking effort.

| Arm | Exercises (590) | All theorems (1,448) | Cost, both sets |
| --- | ---: | ---: | ---: |
| `waterfall` | **386 (65%)** | **1,088 (75%)** | $0.0009 |
| jev-lean + Jev (TypeSafe API) | 247 (42%) | 823 (57%) | $0.46 |
| jev-lean, no model | 247 (42%) | 805 (56%) | $0.0004 |
| jev-lean, hand-written ranking | 240 (41%) | 804 (56%) | $0.0005 |
| every single induction or case split | 245 (42%) | 748 (52%) | $0.0002 |
| automation only | 219 (37%) | 699 (48%) | $0.0001 |
| `aesop` | 196 (33%) | 660 (46%) | under $0.0001 |

**Cost.** Jev's cost is its API bill. The run sent 10.9 million input tokens
over 10,800 calls, and Jev's early-access price in September 2026 was $0.042
per million input tokens, with output free
([OpenRouter listing](https://openrouter.ai/typesafe/jev-1.13)). Every other cost is estimated electricity for the
tactic's own CPU time: each task's time minus the time to elaborate the same
file with `sorry`, at 5 W per busy core and $0.17 per kWh. Waterfall used
about an hour of CPU time across both sets. Jev's local search adds about
$0.0006 of electricity to its bill.

* **Waterfall proves the most.** On the exercises, it proves every task that
  any other arm proves, Jev included. On all theorems, the other arms together
  add 13 tasks to its 1,088.
* **Jev barely changes what jev-lean can prove.** With Jev the harness proves
  247 exercises, the same number as with no model at all; the two differ on 6
  tasks each way. On all theorems Jev gains 18: 823 against 805. The harness's
  fixed candidate list and budget, not the order of candidates, bound what it
  can prove.
* **Jev does rank well.** On the 103 theorems that every jev-lean arm proves
  after consulting its ranker, Jev reaches a proof in 36 attempted transitions
  on average, against 46 with no model. The hand-written ranking does no
  better than catalogue order.
* **Koppel reported Jev at 39% and Waterfall at 27%.** Here Jev in the jev-lean
  harness proves 42% of the exercises, close to his figure. Waterfall proves
  65%. His task list and harness are not public, so his 27% cannot be traced.

Jev answered each ranking call in 0.14 s on average.

Waterfall itself gains most from being handed earlier lemmas. Rerunning its
360 all-theorem failures with every earlier lemma in the file proves 74 more;
with the 32 that Jev ranks most useful, 83 more, for 81% overall. See
[docs/waterfall-with-jev.md](docs/waterfall-with-jev.md).

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

The arms `jev-kev`, `jev-von` and `jev-llm` rank with local models instead;
see [docs/open-jev-models.md](docs/open-jev-models.md).

The jev-lean harness asks a localhost broker to rank a list of Lean-checked
candidate tactics, then searches in that order. `broker/local_broker.py`
speaks the same protocol as jev-lean's TypeSafe broker.

For `jev-typesafe`, the broker sends jev-lean's own Jev request, one `choice`
question whose options are the candidate tactics, to TypeSafe's
`POST /v1/systemone` API. It parses the probabilities as jev-lean does, with
one change. Jev rounds each probability to two decimals, and with many options
the rounded values can miss jev-lean's check that they sum to within 0.01 of 1.
The broker allows the rounding bound, 0.005 per option.

`bench/JevLean` vendors jev-lean with a small port to Lean v4.34.0-rc2,
described in its header. The search keeps jev-lean's default
budgets: 256 attempted transitions, 64 nodes and 16 ranking calls per goal.
Only the wall-clock limit rises, from 10 s to 60 s, so that the clock is never
what stops a search.

If a ranking call fails, the task is not recorded, so a resumed run retries it
rather than silently searching in catalogue order.

## Running it

Tested on Ubuntu x86-64. Requirements: `elan`, `git`, `make`, `python3` 3.10
or newer, `curl` and `sha256sum`.

```sh
./setup.sh
scripts/run_all.sh student --arms "auto induct aesop waterfall jev-stable jev-heuristic"
scripts/run_all.sh solutions --arms "auto waterfall jev-stable"
scripts/report.sh                 # regenerate RESULTS.md
```

Runs append to `results/<arm>.<context>.jsonl` and skip tasks already
recorded, so an interrupted run resumes. Delete a file to rerun its arm.

To rank with Jev itself, set a TypeSafe key and run the `jev-typesafe` arm.
TypeSafe bills the calls:

```sh
TYPESAFE_API_KEY=... scripts/run_all.sh student --arms jev-typesafe
```

The local-model arms, and how to keep their memory in check on a CPU, are
covered in [docs/open-jev-models.md](docs/open-jev-models.md).

## Caveats

* The jev-lean harness is a design similar to Koppel's Rocq harness, but it is
  not his harness.
* Jev's answers vary between identical calls, so a rerun of the Jev arm can
  differ by a few tasks.
* Times are wall-clock on one machine that often ran several arms at once, so
  treat them as rough. RESULTS.md reports tactic time: task time minus the
  time to elaborate the same file with `sorry`.
* Several arms first ran from an earlier local copy of this code. Rerunning
  them from this repository reproduced every outcome. Converting SFBench and
  JevLean to Lean modules, needed for the one module chapter
  (LF/CustomTactics), changed no outcome on either task set.
* The electricity estimates are rough, within a factor of a few. Even at ten
  times the estimate, every local arm costs well under a cent.
* Some basic exercises defeat every arm, including Waterfall. One example is
  `zero_mul` on LF/Induction's custom `Nat`, which Waterfall misses even when
  the definitions are passed in brackets. This benchmark does not diagnose why.
* Waterfall and the baselines use Lean's default `maxHeartbeats`. Every task
  also has a 120 s process limit, which no task reached.

## License

Apache License 2.0. `bench/JevLean` is adapted from jev-lean, also Apache 2.0;
its header lists the changes. sf-in-lean, Kev, Von, llama.cpp and the models
are fetched by `setup.sh` under their own licenses and are not redistributed
here.

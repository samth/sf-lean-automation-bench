# Would Jev help inside Waterfall?

Jev answers one kind of question well: pick among listed options, with a
probability for each. This page asks where Waterfall makes such a choice and
whether a better choice would prove more theorems. The short answer: ordering
Waterfall's search barely matters, but handing Waterfall earlier lemmas
matters a lot. Every earlier lemma in the file already helps as much as an
oracle, and Jev's choice of 32 helps a little more.

All numbers are on this repository's task sets, with Waterfall 0.2.0 at its
default settings. The experiments used 420 paid Jev calls, about 10 cents.

## Waterfall's failures are not near misses

Almost every failure exhausts the effort budget: 194 of 204 failed exercises
stop at 1,000 attempts. More budget helps little.

| Waterfall on its 204 failed exercises | Newly proved |
| --- | ---: |
| 4× effort (and heartbeats) | 8 |
| 16× effort (and heartbeats) | 13 |

At 16×, 139 runs hit Lean's heartbeat limit instead, so that row understates
slightly. Still, a perfect ranker inside the existing search space could at
best stretch the budget, and a larger budget adds only a few percent.

## Where the attempts go

`bench/WfCapture.lean` runs Waterfall through `waterfall.Observe.capture` and
records every attempted action. `experiments/analyze_capture.py` summarizes
the 1,448 theorems (the capture proved 1,092 of them; the benchmark run 1,088).

* **Closers dominate.** Leaf solvers (`rfl`, `omega`, `simp`, `grind`, ...) are
  tried at every node and take 76% of all attempts. In failed searches, 62% of
  all attempts are closers at nodes where none of them succeeds. A Jev `noul`
  question, "can a leaf solver close this goal?", could skip most of them. That
  is worth roughly a 2.5× budget, which by the table above adds little.
* **Structural moves are already well ordered.** Successful proofs average 1.9
  steps; in the trial that finds them, the median is 2 attempts per step.
* **Iterative deepening costs more than ordering.** Successful proofs spend 29
  attempts on earlier depth/strength trials, against 25 on wrong turns within
  the successful trial.
* **Library lemmas are almost never tried.** Library moves cost extra depth,
  so the search rarely reaches them: 971 of 350,000 attempts in failed
  searches. Many Software Foundations proofs instead hinge on citing an
  earlier lemma.

Calling Jev at every node would also be slow: a failed search visits about 140
nodes, so per-node ranking would add about 20 s per theorem.

## Premise selection is the opportunity

Waterfall already accepts extra lemmas: `waterfall [l₁, l₂, ...]`. It rarely
reaches library lemmas on its own, yet many Software Foundations proofs hinge
on citing an earlier one. Each experiment below reruns all 360 all-theorem
failures with a different set of earlier SF theorems passed as rules, using
fully qualified names so that each resolves at the theorem's position.

| Lemmas passed to Waterfall | Recall of cited lemmas | Newly proved, of 360 |
| --- | ---: | ---: |
| Jev, top 32 | 0.72 | **83** |
| Jev, top 16 | 0.67 | 78 |
| Jev, top 64 | 0.76 | 78 |
| Jev, top 8 | 0.57 | 77 |
| every earlier theorem in the file (median 21) | 0.63 | 74 |
| word overlap, top 32 or top 64 | 0.66, 0.76 | 73 |
| word overlap, top 8 or top 16 | 0.41, 0.54 | 59 |
| oracle: exactly the lemmas the reference proof cites | 1.00 | 74 |

Recall counts how many of the lemmas each reference proof cites appear among
those passed. The candidate pool for the rankers is every earlier theorem in
the file and in the chapters it imports, most recent first, capped at 120. Jev
chose among the whole pool in one `choice` question per theorem; the 360 calls
used 2.0 million input tokens, about 8.5 cents.

* **Passing every earlier lemma in the file works about as well as the
  oracle.** It needs no model and proves 74. Its cited-lemma recall is lower,
  but it also supplies useful lemmas that the reference proofs do not cite.
* **Jev does better still.** Its top 32 proves 83, lifting Waterfall from
  1,088 to 1,171 of the 1,448 theorems (81%). Jev and every-lemma overlap
  heavily: 69 theorems are proved by both, 14 only with Jev and 5 only with
  every lemma. Together they prove 88.
* **More lemmas do not always help.** Each rule is also a move Waterfall tries
  at every node, so irrelevant rules dilute its budget. Jev's best depth is
  32; at 64 it drops back to 78. Word overlap needs 32 to catch up with the
  every-lemma list.
* **Rules cost little time.** The median failed task took 6 to 10 s with rules
  passed, depending on how many.

## A design that cannot lose theorems

Passing extra lemmas unconditionally is not free. Rerunning the 1,088 theorems
Waterfall already proves with every earlier lemma in the file loses 50 of
them, so as a default it would gain only 24 net.

Instead, run plain Waterfall first. Only if it fails, rerun it with extra
lemmas: every earlier lemma in the file, which needs no model, or Jev's top
32, which costs one call of about 5,600 input tokens ($0.0002). Waterfall's
existing proofs are untouched, and the retry adds 74 or 83 theorems on this
set, from 75% to 80% or 81%.

## Reproducing

```sh
scripts/run_all.sh solutions --arms waterfall        # baseline
python3 scripts/run.py --arm wf-capture --context solutions
python3 experiments/analyze_capture.py
F=experiments/waterfall-failures.solutions.txt
python3 experiments/premises.py rank --ranker file --ids $F --out rank-file.json
SYSTEMONE_API_KEY=... python3 experiments/premises.py rank --ranker jev --cap 120 --ids $F --out rank-jev.json
python3 experiments/premises.py rules --ranking rank-jev.json --k 32 --out rules-jev-k32.json
ORACLE_RULES=rules-jev-k32.json python3 scripts/run.py --arm waterfall-rules --context solutions --ids-file $F
```

The oracle lemma lists (`experiments/oracle-lemmas.*.json`) come from scanning
each reference proof for names of earlier SF theorems, excluding tactic names.

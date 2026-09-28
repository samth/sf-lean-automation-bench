# Would Jev help inside Waterfall?

Jev answers one kind of question well: pick among listed options, with a
probability for each. This page asks where Waterfall makes such a choice and
whether a better choice would prove more theorems. The short answer: ordering
Waterfall's search barely matters, but choosing which earlier lemmas to hand
Waterfall matters a lot, and Jev does that well with one call per theorem.

All numbers are on this repository's task sets, with Waterfall 0.2.0 at its
default settings. The experiments used 60 paid Jev calls, about 1.4 cents.

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

Waterfall already accepts extra lemmas: `waterfall [l₁, l₂, ...]`. Of the 360
all-theorem failures, 223 have reference proofs that cite earlier SF lemmas.

| Lemmas passed to Waterfall | Newly proved, of 223 |
| --- | ---: |
| oracle: exactly those the reference proof cites | 74 |
| top 16 by lexical overlap with the goal | 44 |
| top 8 by lexical overlap | 41 |
| top 4 by lexical overlap | 31 |

With the oracle, Waterfall would prove 1,162 of the 1,448 theorems (80%). On
the 590 exercises, the oracle proves 16 of 109 failures strictly and 22 more
using earlier exercises, which are admitted in that setting.

The candidate pool for a theorem is every theorem before it in its chapter and
in the chapters it imports, up to 120 (median 109). On a random sample of 60
of the 223 tasks, Jev chose among the whole pool in one `choice` question per
theorem (`experiments/premises.py`):

| Ranker, top 8 | Recall of cited lemmas | Newly proved, of 60 |
| --- | ---: | ---: |
| oracle | 1.00 | 19 |
| Jev | 0.73 | 17 |
| lexical overlap | 0.51 | 11 |

Jev comes within two theorems of the oracle. Each call cost about 5,700 input
tokens, or $0.0002. Jev proved 8 tasks that lexical ranking missed and lexical
ranking proved 2 that Jev missed, so the sample favors Jev without settling
the size of the gap.

## A design that cannot lose theorems

Run plain Waterfall first. Only if it fails, ask Jev once for the most useful
earlier lemmas and rerun `waterfall [top 8]`. Plain Waterfall's successes are
untouched, and only failures pay for a Jev call and a second search.
Extrapolating the sample, that would lift Waterfall from about 75% to about
80% of the 1,448 theorems, for well under a cent per failed theorem.

## Reproducing

```sh
scripts/run_all.sh solutions --arms waterfall        # baseline
python3 scripts/run.py --arm wf-capture --context solutions
python3 experiments/analyze_capture.py
python3 experiments/premises.py --ranker lexical --k 8 --out rules.json
SYSTEMONE_API_KEY=... python3 experiments/premises.py --ranker jev --k 8 --sample 60 --out rules-jev.json
ORACLE_RULES=rules-jev.json python3 scripts/run.py --arm waterfall-rules --context solutions \
  --ids-file experiments/sample60-ids.txt
```

The oracle lemma lists (`experiments/oracle-lemmas.*.json`) come from scanning
each reference proof for names of earlier SF theorems, excluding tactic names.

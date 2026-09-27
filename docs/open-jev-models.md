# Open Jev-style models in the jev-lean harness

The [README](../README.md) compares Waterfall, jev-lean ranked by Jev itself,
and standard Lean automation. Before a Jev key was available, the jev-lean
harness was also run with open models in Jev's place. This page records those
runs. Per-volume counts are in [RESULTS.md](../RESULTS.md).

## Results

| Ranker in the jev-lean harness | Exercises (590) | All theorems (1,448) | Cost, both sets |
| --- | ---: | ---: | ---: |
| Jev (TypeSafe API), for reference | 247 (42%) | 823 (57%) | $0.46 |
| [Kev-0.8B](https://github.com/jaredpalmer/kev) | 246 (42%) | 814 (56%) | about $0.05 |
| [Von 1.2](https://github.com/wfzyx/von) | 239 (41%) | 801 (55%) | about $0.03 |
| prompted Qwen2.5-Coder-1.5B | 240 (41%) | not run | about $0.01 |
| no model (catalogue order) | 247 (42%) | 805 (56%) | under $0.001 |

Search effort on the tasks that every jev-lean arm proves after consulting its
ranker; fewer attempted transitions means a better ranking:

| Ranker | 32 exercises | 103 theorems |
| --- | ---: | ---: |
| Jev | 41.8 | 36.2 |
| Kev-0.8B | 41.6 | 38.5 |
| Von 1.2 | 56.2 | 47.3 |
| prompted Qwen2.5-Coder-1.5B | 57.6 | not run |
| no model | 55.0 | 46.3 |

Kev-0.8B, a 0.8B model on a laptop-class CPU, ranks about as well as Jev. Von
and the prompted code model rank no better than catalogue order. No ranker
changes coverage much, because the harness's candidate list and budget bound
what it can prove.

The costs are electricity. They assume a busy CPU core draws 5 W, a model
server keeps 4 cores busy while it answers, and electricity costs $0.17 per
kWh. They are rough, within a factor of a few.

## How the models are wired in

`broker/local_broker.py` speaks jev-lean's localhost broker protocol.

* **Kev and Von** are served locally through TypeSafe's `POST /v1/systemone`
  API. The broker sends jev-lean's own Jev request, one `choice` question whose
  options are the candidate tactics, and parses the answer as jev-lean does.
  Kev takes the request unchanged. Von accepts only string option
  descriptions, so each option is sent as the bare tactic text. Kev (Jared
  Palmer) fine-tunes Qwen3.5 with a decision head and reports accuracy within
  a few points of Jev on held-out sources. Von is a 395M ModernBERT encoder
  whose option scores do not depend on option order.
* **Prompted Qwen** is a general code model, not a Jev-style one. The broker
  gives each candidate a one-character label and reads the label
  probabilities from one forward pass through llama.cpp. It was a first
  approximation.

Run them with `./setup.sh --jev-like` (Kev and Von, needs
[uv](https://docs.astral.sh/uv/)) or `./setup.sh --llm` (llama.cpp and two
GGUF models, 6.6 GB), then `scripts/run_all.sh <set> --arms "jev-kev jev-von
jev-llm"`. These arms get a 600 s search wall budget instead of 60 s, because
they run on a CPU.

## Memory on a CPU

A Kev server's memory grows steeply with the length of the goal it ranks: 5.7
GB for a 10 KB request and 8.7 GB for 19 KB here, and over 16 GB for 32 KB.
Long Type Systems goals therefore need special handling.

* `run_all.sh` runs each model server under a hard cgroup memory limit
  (`MODEL_MEMORY_MAX`, default 10G) where `systemd-run --user` works, so a
  spike stops the server rather than starving the machine.
* `MODEL_MAX_REQUEST_BYTES` makes the broker refuse larger requests. Those
  tasks are recorded as `ranker_oversize` and count as unproved.
* `scripts/run_capped.sh` restarts a run whose model servers exceed a memory
  cap or die, and gives up after three restarts with no new result.

The Kev run on all theorems finished with:

```sh
OMP_NUM_THREADS=4 MODEL_MEMORY_MAX=10G MODEL_MAX_REQUEST_BYTES=20000 KEV_ATTN=sdpa \
  nice -n 19 taskset -c 14-19 scripts/run_capped.sh 11 solutions --arms jev-kev --model-jobs 1
```

## Caveats

* Kev's last 209 theorems on the all-theorems set, all in the Type Systems
  volume, ran with PyTorch's memory-efficient attention (`KEV_ATTN=sdpa`)
  instead of Kev's CPU default, and with requests over 20 KB refused. The two
  compute the same attention up to floating-point rounding. Three of those
  tasks were refused as too large, and count as unproved.
* Von reads at most 8,192 tokens. A few Type Systems goals are longer; Von
  warns and answers anyway, so its rankings on them may be degraded.
* Kev and Von ran on a CPU. Their latency here says nothing about their speed
  on a GPU.
* These arms first ran from an earlier local copy of the same broker and
  jev-lean port. Rerunning the deterministic arms from this repository
  reproduced every outcome.

## Other candidates

* **Laya** (421M encoder) accepts jev-lean's request unchanged and answers in
  under a second on a CPU. Its options share a token budget of about 20 short
  options, and jev-lean often sends more; past that point identical options
  received different ranks in a test here, so it was not run.
* **Kev-4B to Kev-27B** and **Bespoke Nimble-9B** need a GPU. Kev and Nimble
  ship Modal deployments that serve the same API; point the broker at one with
  `--ranker systemone --systemone-url URL` and `SYSTEMONE_API_KEY`.

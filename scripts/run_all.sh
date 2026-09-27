#!/usr/bin/env bash
# Run the comparison arms over one task set, starting and stopping the local
# rank brokers and llama.cpp servers they need.
#
#   scripts/run_all.sh <student|solutions> [--jobs N] [--arms "a b ..."]
#                      [--model-jobs N] [--llama-server PATH] [--filter REGEX]
#
# To keep the machine responsive, run under nice and taskset, e.g.
#   OMP_NUM_THREADS=4 nice -n 19 taskset -c 14-19 scripts/run_all.sh solutions \
#     --arms jev-kev --model-jobs 2
#
# Arms: auto induct aesop waterfall jev-stable jev-heuristic jev-kev jev-kev4b
# jev-von jev-llm jev-llm7b jev-typesafe.  jev-kev* and jev-von need
# `setup.sh --jev-like`; jev-llm* need `setup.sh --llm`; jev-typesafe ranks with
# Jev itself and needs TYPESAFE_API_KEY (calls are billed by TypeSafe).  Results append to results/<arm>.<context>.jsonl; finished task ids
# are skipped, so an interrupted run resumes where it stopped.
set -euo pipefail
cd "$(dirname "$0")/.."

context=${1:?usage: $0 <student|solutions> [options]}
shift
jobs=12
model_jobs=4
arms="auto induct aesop waterfall jev-stable jev-heuristic jev-kev jev-von"
llama_server=$(ls tools/llama-*/llama-server 2>/dev/null | head -1 || true)
filter=""
while [[ $# -gt 0 ]]; do
  case $1 in
    --jobs) jobs=$2; shift 2 ;;
    --model-jobs) model_jobs=$2; shift 2 ;;
    --arms) arms=$2; shift 2 ;;
    --llama-server) llama_server=$2; shift 2 ;;
    --filter) filter=$2; shift 2 ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
done

export JEV_MAX_WALL_MS=${JEV_MAX_WALL_MS:-60000}
mkdir -p logs results
# Servers start inside $(...) subshells, so their process-group ids go to a
# file rather than a shell array; each runs under setsid so that killing its
# group also stops children such as the Python process behind `uv run`.
pidfile=$(mktemp "${TMPDIR:-/tmp}/run_all.XXXXXX")
cleanup() {
  while read -r pgid; do kill -- "-$pgid" 2>/dev/null || true; done <"$pidfile"
  rm -f "$pidfile"
}
trap cleanup EXIT
spawn() {  # spawn <log> <command...>: start a server in its own process group
  local log=$1; shift
  setsid "$@" >"$log" 2>&1 &
  echo $! >>"$pidfile"
}

free_port() { python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1])'; }

wait_for() {  # wait_for <logfile> <pattern>
  for _ in $(seq 1 600); do
    grep -q "$2" "$1" 2>/dev/null && return 0
    sleep 1
  done
  echo "timed out waiting for $2 in $1" >&2; exit 1
}

start_broker() {  # start_broker <ranker> <label> [llm-url]; prints the port
  local port; port=$(free_port)
  local extra=()
  [[ -n ${3:-} ]] && extra=(--llm-url "$3")
  spawn "logs/broker-$2.log" python3 broker/local_broker.py --ranker "$1" --port "$port" \
    "${extra[@]}" --stats "results/broker-$2.$context.json"
  wait_for "logs/broker-$2.log" "ready on"
  echo "$port"
}

start_systemone() {  # start_systemone <kev|von> <model> <label>; prints the URL
  local port; port=$(free_port)
  if [[ $1 == kev ]]; then
    [[ -d tools/kev ]] || { echo "tools/kev missing; run setup.sh --jev-like" >&2; exit 1; }
    spawn "logs/$3.log" uv run --directory tools/kev --extra serve \
      python -m kev.serve --run "$2" --port "$port"
    wait_for "logs/$3.log" "Uvicorn running"
  else
    [[ -d tools/von ]] || { echo "tools/von missing; run setup.sh --jev-like" >&2; exit 1; }
    spawn "logs/$3.log" uv run --directory tools/von von serve --host 127.0.0.1 --port "$port"
    wait_for "logs/$3.log" "Uvicorn running"
  fi
  echo "http://127.0.0.1:$port"
}

start_systemone_broker() {  # start_systemone_broker <url> <label> [extra broker args]; prints the port
  local port; port=$(free_port)
  spawn "logs/broker-$2.log" python3 broker/local_broker.py --ranker systemone \
    --systemone-url "$1" --port "$port" "${@:3}" --stats "results/broker-$2.$context.json"
  wait_for "logs/broker-$2.log" "ready on"
  echo "$port"
}

# Jev-style servers on a CPU are much slower than hosted Jev.  Their arms get a
# 10-minute search wall budget, so jev-lean's caps on attempted transitions and
# ranking calls, not the clock, end each search.
model_arm() {  # model_arm <label> <broker port>
  JEV_MAX_WALL_MS=600000 run --arm jev --label "$1" --broker-port "$2" --jobs "$model_jobs" --timeout 900
}

start_llama() {  # start_llama <model file> <label>; prints the URL
  [[ -x $llama_server ]] || { echo "llama-server not found; run setup.sh --llm" >&2; exit 1; }
  [[ -f models/$1 ]] || { echo "models/$1 missing; run setup.sh --llm" >&2; exit 1; }
  local port; port=$(free_port)
  spawn "logs/llama-$2.log" env LD_LIBRARY_PATH="$(dirname "$llama_server"):${LD_LIBRARY_PATH:-}" \
    "$llama_server" -m "models/$1" -c 32768 -np 4 -t "$(( $(nproc) * 4 / 5 ))" \
    --host 127.0.0.1 --port "$port"
  wait_for "logs/llama-$2.log" "listening on"
  echo "http://127.0.0.1:$port"
}

run() { python3 scripts/run.py --context "$context" --filter "$filter" "$@"; }

for arm in $arms; do
  case $arm in
    auto|induct|aesop|waterfall) run --arm "$arm" --jobs "$jobs" ;;
    jev-stable) run --arm jev --label "$arm" --broker-port "$(start_broker stable "$arm")" --jobs "$jobs" ;;
    jev-heuristic) run --arm jev --label "$arm" --broker-port "$(start_broker heuristic "$arm")" --jobs "$jobs" ;;
    jev-kev|jev-kev4b)
      model=jaredpalmer/kev-0.8b@9a45d25eb2ab761841196625383fa1dff0e56c1e
      [[ $arm == jev-kev4b ]] && model=jaredpalmer/kev-4b
      url=$(start_systemone kev "$model" "$arm-server")
      model_arm "$arm" "$(start_systemone_broker "$url" "$arm")"
      ;;
    jev-von)
      url=$(start_systemone von - "$arm-server")
      model_arm "$arm" "$(start_systemone_broker "$url" "$arm" --string-criteria)"
      ;;
    jev-typesafe)
      : "${TYPESAFE_API_KEY:?jev-typesafe needs TYPESAFE_API_KEY}"
      port=$(SYSTEMONE_API_KEY=$TYPESAFE_API_KEY start_systemone_broker https://api.typesafe.ai "$arm")
      run --arm jev --label "$arm" --broker-port "$port" --jobs "$jobs"
      ;;
    jev-llm|jev-llm7b)
      model=qwen2.5-coder-1.5b-instruct-q8_0.gguf
      [[ $arm == jev-llm7b ]] && model=qwen2.5-coder-7b-instruct-q4_k_m.gguf
      url=$(start_llama "$model" "$arm")
      # The model shares the CPU with Lean, so these arms run fewer Lean jobs.
      run --arm jev --label "$arm" --broker-port "$(start_broker llm "$arm" "$url")" --jobs "$model_jobs"
      ;;
    *) echo "unknown arm $arm" >&2; exit 2 ;;
  esac
done

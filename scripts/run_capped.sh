#!/usr/bin/env bash
# Run scripts/run_all.sh with a memory cap on its model servers.
#
#   scripts/run_capped.sh <cap-GB> <run_all.sh arguments...>
#
# On a CPU, a long-running model server (Kev in particular) can grow steadily.
# This wrapper checks the resident memory of every model server every 3 s.
# When the total passes the cap, or a server has died (for example at the
# cgroup limit set by run_all.sh), it stops the run, which also stops the
# servers, and starts it again.  run_all.sh skips tasks that already have a
# result, so a restart loses at most the tasks that were in flight.  After
# three restarts in a row without a new result, it gives up.
set -euo pipefail
cd "$(dirname "$0")/.."
cap_gb=${1:?usage: $0 <cap-GB> <run_all.sh arguments...>}
shift
cap_kb=$((cap_gb * 1024 * 1024))
export MALLOC_ARENA_MAX=${MALLOC_ARENA_MAX:-2}   # limit glibc allocator fragmentation
# Model servers started from this checkout (their command lines name tools/).
servers="\.venv/bin/python -m kev\.serve|\.venv/bin/von serve|tools/llama-[^/]*/llama-server"

server_rss_kb() {
  local pids
  pids=$(pgrep -f "$servers" || true)
  [[ -z $pids ]] && { echo 0; return; }
  ps -o rss= -p $(echo "$pids" | paste -sd,) | awk '{s += $1} END {print s + 0}'
}

results_count() { cat results/*.jsonl 2>/dev/null | wc -l; }
stalled=0
while true; do
  before=$(results_count)
  setsid scripts/run_all.sh "$@" &
  run=$!
  capped=0
  seen=0
  gone=0
  while kill -0 "$run" 2>/dev/null; do
    sleep 3
    rss=$(server_rss_kb)
    if (( rss > 0 )); then seen=1; gone=0; elif (( seen )); then gone=$((gone + 1)); fi
    reason=""
    (( rss > cap_kb )) && reason="model servers at $((rss / 1024)) MB, over the ${cap_gb} GB cap"
    (( gone >= 5 )) && reason="a model server exited"
    if [[ -n $reason ]]; then
      echo "$(date '+%F %T') $reason; restarting" >&2
      capped=1
      kill -TERM -- "-$run" 2>/dev/null || true
      for _ in $(seq 60); do kill -0 "$run" 2>/dev/null || break; sleep 1; done
      kill -KILL -- "-$run" 2>/dev/null || true
      pkill -f "$servers" 2>/dev/null || true   # in case the run's own cleanup did not finish
      break
    fi
  done
  if (( capped )); then
    rm -f bench/ctx-*/Tasks/tmp*.lean
    if (( $(results_count) > before )); then stalled=0; else stalled=$((stalled + 1)); fi
    if (( stalled >= 3 )); then
      echo "$(date '+%F %T') three restarts without a new result; giving up" >&2
      exit 1
    fi
    continue
  fi
  wait "$run"
  exit $?
done

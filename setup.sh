#!/usr/bin/env bash
# Prepare the benchmark: fetch sf-in-lean at a pinned commit, generate its
# student and solutions variants, extract tasks, and build both context
# workspaces.  With --jev-like, also install two open Jev-style decision
# models, Kev and Von (needs uv).  With --llm, fetch llama.cpp (CPU build) and
# two general code models for the prompted-LLM arms.
#
# Requirements: git, make, python3 (3.10+), curl, elan (for lake/lean).
set -euo pipefail
cd "$(dirname "$0")"

SFL_REPO=https://github.com/plclub/sf-in-lean
SFL_REV=dcf44331b94b0918ec9655c06a459390e3924177
LLAMA_TAG=b11205
KEV_REV=5920c5fe4ca8e0970ed4209ac2c9b8e18bea5109
VON_REV=fb6e7a937e4fc6b6e72b2ce5035edd56bc370e54
MODELS=(
  "qwen2.5-coder-1.5b-instruct-q8_0.gguf|https://huggingface.co/Qwen/Qwen2.5-Coder-1.5B-Instruct-GGUF/resolve/main/qwen2.5-coder-1.5b-instruct-q8_0.gguf|507de59046601282ba768a9789900e6ccf60ed93ddf346730b7c68eb0715bc47"
  "qwen2.5-coder-7b-instruct-q4_k_m.gguf|https://huggingface.co/Qwen/Qwen2.5-Coder-7B-Instruct-GGUF/resolve/main/qwen2.5-coder-7b-instruct-q4_k_m.gguf|509287f78cb4d4cf6b3843734733b914b2c158e43e22a7f4bf5e963800894d3c"
)

want_llm=0
want_jev_like=0
for arg in "$@"; do
  case $arg in
    --llm) want_llm=1 ;;
    --jev-like) want_jev_like=1 ;;
    *) echo "usage: $0 [--jev-like] [--llm]" >&2; exit 2 ;;
  esac
done

mkdir -p vendor
if [[ ! -d vendor/sf-in-lean/.git ]]; then
  git clone "$SFL_REPO" vendor/sf-in-lean
fi
git -C vendor/sf-in-lean fetch --quiet origin "$SFL_REV" || true
git -C vendor/sf-in-lean checkout --quiet "$SFL_REV"

if [[ ! -d vendor/sf-in-lean/_out/ts/solutions/lean ]]; then
  echo "== building sf-in-lean student and solutions variants (several minutes)"
  make -C vendor/sf-in-lean student solutions
fi

echo "== extracting tasks and building context workspaces"
python3 scripts/extract.py

fetch() {  # fetch <repo> <rev> <dir>
  [[ -d $3/.git ]] || git clone --quiet "$1" "$3"
  git -C "$3" fetch --quiet origin "$2" || true
  git -C "$3" checkout --quiet "$2"
}

if [[ $want_jev_like == 1 ]]; then
  command -v uv >/dev/null || { echo "--jev-like needs uv (https://docs.astral.sh/uv/)" >&2; exit 1; }
  mkdir -p tools
  fetch https://github.com/jaredpalmer/kev "$KEV_REV" tools/kev
  fetch https://github.com/wfzyx/von "$VON_REV" tools/von
  (cd tools/kev && uv sync --extra serve)
  (cd tools/von && uv sync)
  echo "Kev and Von download their weights from Hugging Face on first use."
fi

if [[ $want_llm == 1 ]]; then
  if [[ "$(uname -s)-$(uname -m)" != "Linux-x86_64" ]]; then
    echo "--llm downloads the Linux x86-64 CPU build of llama.cpp; on other" >&2
    echo "platforms install llama-server yourself and pass --llama-server to run_all.sh" >&2
    exit 1
  fi
  mkdir -p tools models
  if [[ ! -x tools/llama-$LLAMA_TAG/llama-server ]]; then
    curl -fL -o tools/llama.tar.gz \
      "https://github.com/ggml-org/llama.cpp/releases/download/$LLAMA_TAG/llama-$LLAMA_TAG-bin-ubuntu-x64.tar.gz"
    tar xzf tools/llama.tar.gz -C tools && rm tools/llama.tar.gz
  fi
  for entry in "${MODELS[@]}"; do
    IFS='|' read -r file url sum <<<"$entry"
    if [[ ! -f models/$file ]]; then
      curl -fL -o "models/$file" "$url"
    fi
    echo "$sum  models/$file" | sha256sum -c -
  done
fi
echo "== setup complete; run scripts/run_all.sh <student|solutions>"

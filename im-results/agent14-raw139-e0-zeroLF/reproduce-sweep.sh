#!/usr/bin/env bash
set -euo pipefail
base=im-results/agent14-raw139-e0-zeroLF
work=.tmp/a48-e0sweep-ZeroLF
mkdir -p "$work/imports" "$work/build" 
python3 im-results/agent13-coverage/unpack.py
python3 "$base/replay.py"
python3 tools/lean_compile_closure.py "$base/E0LFResidualAudit.lean" \
  --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-zeroLF-residual-audit \
  --theorem BB6Coverage.Agent14E0LFResidual10338.never \
  --artifact-name raw139-e0sweep-ZeroLF-certified | tee "$work/log"

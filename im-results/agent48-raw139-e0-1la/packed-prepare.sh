#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
work="$PWD/.tmp/a48-e0long"
mkdir -p "$work/imports" "$work/build"
cp "$base/OneLAPackedCore.lean" "$work/imports/"
python3 "$base/emit-packed-cycle.py" "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/OneLAPackedConfigs.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 2 \
  --manifest "$work/core-manifest.json" --provenance-input "$base/emit-packed-cycle.py" \
  | tee "$work/core.log"
! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "$work/core.log"
git rev-parse HEAD > "$work/source-sha"

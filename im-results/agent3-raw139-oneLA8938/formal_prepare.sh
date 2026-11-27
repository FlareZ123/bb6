#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent3-raw139-oneLA8938"
work=/tmp/8938lean
mkdir -p "$work"
cat "$base"/formal.tar.xz.b64.{1,2} | base64 -d > "$work/formal.tar.xz"
printf '%s  %s\n' d1faec63a5289e0ec778ade424d19f9bf356061610383d4b8adcda44dadf589a "$work/formal.tar.xz" | sha256sum -c -
tar -xJf "$work/formal.tar.xz" -C "$work"
python3 "$base/unpack.py"
python3 "$base/unpack_affine.py"
python3 im-results/agent13-coverage/unpack.py
export PYTHONPATH="$base"
python3 "$work/gen_fastlookup.py"
python3 "$base/affine8938.py" 6 | tee "$work/affine.log"
grep -F 'SUCCESS 1835426 76853158 42613560 15192' "$work/affine.log"
python3 "$work/trace8938.py" growth 3000
python3 "$work/trace8938.py" seed 3000
python3 "$work/emit_main8938.py"
test "$(find "$work/generated" -name '*.lean' | wc -l)" = 127
python3 tools/lean_compile_closure.py "$work/FastLookup.lean" "$work/AffineFinish.lean" \
  --source-root "$work" --workdir "$work/build" --jobs 2 \
  --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
  --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
  --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
  --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
  --manifest "$work/core-manifest.json" | tee "$work/core.log"
! grep -E 'sorryAx|native_decide|ofReduceBool' "$work/core.log"
git rev-parse HEAD > "$work/source-sha"

#!/usr/bin/env bash
set -euo pipefail
work=/tmp/8938lean
test "$(git rev-parse HEAD)" = "$(cat "$work/source-sha")"
export LEAN_PATH="$work/build"
mkdir -p /tmp/8938shard
mapfile -t files < <(find "$work/generated" -name '*.lean' | LC_ALL=C sort)
test "${#files[@]}" = 127
for i in "${!files[@]}"; do
  if (( i % 16 != SHARD )); then continue; fi
  f="${files[i]}"; name="$(basename "$f" .lean)"
  echo "Checking $name"
  lean -j 1 --root="$work/generated" -o "/tmp/8938shard/$name.olean" "$f" 2>&1 | tee "/tmp/8938shard/$name.log"
  test -s "/tmp/8938shard/$name.olean"
  ! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "/tmp/8938shard/$name.log"
done

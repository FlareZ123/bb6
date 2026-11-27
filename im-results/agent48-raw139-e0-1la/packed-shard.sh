#!/usr/bin/env bash
set -euo pipefail
work="$PWD/.tmp/a48-e0long"
out="$PWD/.tmp/a48-e0long-shard"
test "$(git rev-parse HEAD)" = "$(cat "$work/source-sha")"
test "$SHARD" -ge 0 && test "$SHARD" -lt 8
mkdir -p "$out"
cp "$work/source-sha" "$out/"
export LEAN_PATH="$work/build"
cd "$work/imports"
i=0
while read -r name; do
  if (( i % 8 == SHARD )); then
    echo "Checking $name"
    lean -j 1 -o "$out/$name.olean" "$name.lean" 2>&1 | tee "$out/$name.log"
    test -s "$out/$name.olean"
    ! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "$out/$name.log"
    sha256sum "$name.lean" > "$out/$name.source.sha256"
  fi
  i=$((i+1))
done < shard-modules.txt
(cd "$out"; sha256sum *.olean > objects.sha256)

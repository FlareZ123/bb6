#!/usr/bin/env bash
set -euo pipefail
mkdir -p "$WORK"
tar -xzf /tmp/box12-common/box12-common.tar.gz -C "$WORK"
cd "$WORK"
export LEAN_PATH="$WORK:$WORK/tree:$DEPS"
shopt -s nullglob
files=(tree/Box12E"${E}"S*.lean)
if (("${#files[@]}")); then
  printf '%s\0' "${files[@]}" | xargs -0 -n1 -P2 bash -c 'echo "Checking $1"; lean -j1 -o "${1%.lean}.olean" "$1"' _
fi
lean -j1 -o "tree/Box12E${E}.olean" "tree/Box12E${E}.lean"

#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
HERE="$ROOT/im-results/agent49-domain-blockfar"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
tar -xJf "$HERE/domain-source.tar.xz" -C "$WORK"
for f in BlockMacro BlockFAR RangeCheck BlockFARBridge; do cp "$ROOT/im-results/agent13-block-far/$f.lean" "$WORK/"; done
for f in Frontier OneHalt; do cp "$ROOT/im-results/agent8-coverage-contract/$f.lean" "$WORK/"; done
cd "$WORK"
python3 build_box7.py
export LEAN_PATH="$WORK${LEAN_PATH:+:$LEAN_PATH}"
for f in Frontier OneHalt BlockMacro BlockFAR RangeCheck BlockFARBridge DomainBlockFAR DomainBlockFARBridge BoxOneHalt BoxCodes Box7Base Box7AllData Box7AllProof Box7Cover; do
  lean -o "$f.olean" "$f.lean"
done

#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ARCHIVE="$ROOT/im-results/agent35-d-regular-certificate/LeanSources.tar.xz.b64"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

base64 -d "$ARCHIVE" | tar -xJf - -C "$TMP"
LEAN="${LEAN:-lean}"
export LEAN_PATH="$TMP:$ROOT/im-results/agent2-cryptid-continuity:$ROOT/im-results/agent4-cryptid-macro-replay"

(cd "$TMP" && "$LEAN" -o "$TMP/DRegular.olean" DRegular.lean)
"$LEAN" -o "$TMP/DRegularShift.olean" "$ROOT/im-results/agent2-cryptid-continuity/DRegularShift.lean"
"$LEAN" -o "$TMP/First10AffineBridge.olean" "$ROOT/im-results/agent4-cryptid-macro-replay/First10AffineBridge.lean"
python3 "$ROOT/im-results/agent4-cryptid-macro-replay/cryptid_A_step2_replay.py"

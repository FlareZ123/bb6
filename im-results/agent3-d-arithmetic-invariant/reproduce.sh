#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
base64 -d InvariantObstruction.lean.xz.b64 | xz -d > "$tmp/InvariantObstruction.lean"
echo "af026d4a45841a6ae90b47fd38857be91fd81498e2aeb1295b606b58d4ad2b45  $tmp/InvariantObstruction.lean" | sha256sum -c
lean "$tmp/InvariantObstruction.lean"

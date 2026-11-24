#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
DEST=${1:-/tmp/agent2-abe}
mkdir -p "$DEST"
cd "$DEST"
base64 -d "$HERE/abe-stage1.tar.xz.b64" > abe-stage1.tar.xz
echo '2ab21be1a676a9bd01bdaabfde335cfc8c890c8f8d63fa5b6c5a6783132667e8  abe-stage1.tar.xz' | sha256sum -c
tar -xJf abe-stage1.tar.xz
base64 -d "$ROOT/im-results/agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > Boundary.lean
echo '0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  Boundary.lean' | sha256sum -c
base64 -d "$ROOT/im-results/agent32-d-route-dag/route-proof.tar.xz.b64" | tar -xJ RouteFront.lean
cp "$ROOT/im-results/agent32-cryptid-padding/"{Generic,BoundaryPadding}.lean .
export LEAN_PATH=.
for module in Boundary Generic BoundaryPadding RouteFront ABEReturn ABEGraph; do lean -o "$module.olean" "$module.lean"; done

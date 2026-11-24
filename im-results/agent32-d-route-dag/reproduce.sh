#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cd "$work"
base64 -d "$here/route-proof.tar.xz.b64" > route-proof.tar.xz
echo '8541613dfcd228fed738f28def38ba759ec7e9002f6b7f741b74a9592f86a4c3  route-proof.tar.xz' | sha256sum -c
tar -xJf route-proof.tar.xz
base64 -d "$here/../agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > Boundary.lean
echo '0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  Boundary.lean' | sha256sum -c
cp "$here/../agent32-cryptid-padding/Generic.lean" "$here/../agent32-cryptid-padding/BoundaryPadding.lean" "$here/EQ1TerminalBlank.lean" "$here/RouteMembership.lean" .
export LEAN_PATH="$PWD"
lean --version
for mod in Boundary Generic BoundaryPadding EQ1TerminalBlank RouteFront RouteGraphChunks RouteArithmetic RouteBridge RouteMembership; do
  lean -o "$mod.olean" "$mod.lean"
done

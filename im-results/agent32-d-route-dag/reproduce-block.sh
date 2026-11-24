#!/bin/bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cd "$work"
for item in route-proof route-block-lean route-block-cpp; do
 base64 -d "$here/$item.tar.xz.b64" > "$item.tar.xz"
done
echo '8541613dfcd228fed738f28def38ba759ec7e9002f6b7f741b74a9592f86a4c3  route-proof.tar.xz' | sha256sum -c
echo '3b96983829a6da14cbdfd0db93216031d9891227b81467a84f742b3124cc7c3b  route-block-lean.tar.xz' | sha256sum -c
echo 'e9a5b5c514abb9ab3cc28e99c7334f4b4fdf3f882519b1f4f63be42b41033551  route-block-cpp.tar.xz' | sha256sum -c
for item in route-proof route-block-lean route-block-cpp; do tar -xJf "$item.tar.xz"; done
base64 -d "$here/../agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > Boundary.lean
echo '0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  Boundary.lean' | sha256sum -c
cp "$here/../agent32-cryptid-padding/Generic.lean" "$here/../agent32-cryptid-padding/BoundaryPadding.lean" "$here/EQ1TerminalBlank.lean" "$here/RouteMembership.lean" .
export LEAN_PATH="$PWD"
for mod in Boundary Generic BoundaryPadding EQ1TerminalBlank RouteFront RouteGraphChunks RouteArithmetic RouteBridge RouteMembership RouteTokens RouteAllFront RouteBlock RoutePartial RouteReplayExact RouteHalt; do
 lean -o "$mod.olean" "$mod.lean"
done
g++ -std=c++17 -O3 dblock.cpp -lgmpxx -lgmp -o dblock
./dblock 100000 endpoint.txt dag.tsv 9
python3 ddirect.py 100000 endpoint.txt
if [[ $# -gt 0 ]]; then ./dblock "$1" "$here/endpoint-$1.txt" dag.tsv 9; fi

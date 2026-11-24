#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
base64 -d "$here/OneSided.tar.xz.b64" > "$tmp/OneSided.tar.xz"
echo "c11d6e571c5bdd2c963a65b3bd34fecfec1d65cf52d6b79b4ada7c3195ee4c40  $tmp/OneSided.tar.xz" | sha256sum -c -
tar -xJf "$tmp/OneSided.tar.xz" -C "$tmp"
base64 -d "$root/im-results/agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > "$tmp/Boundary.lean"
echo "0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  $tmp/Boundary.lean" | sha256sum -c -
cd "$tmp"
export LEAN_PATH="$tmp${LEAN_PATH:+:$LEAN_PATH}"
lean --version
for m in Boundary OneSidedRank OneSidedCertificate OneSidedBounds OneSidedSource OneSidedTotal; do
  lean -o "$m.olean" "$m.lean" | tee "$m.log"
  if grep -E 'sorryAx|native_decide|uses .sorry.' "$m.log"; then exit 1; fi
done

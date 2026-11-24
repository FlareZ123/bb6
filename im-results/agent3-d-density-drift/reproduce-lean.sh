#!/usr/bin/env bash
# Lean 4.36.0-rc2; run from this directory or any location.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$tmp"
base64 -d "$here/DriftLean.tar.xz.b64" > DriftLean.tar.xz
echo 'c2b5b7998709bfdec6746e08f5f9b9e514b4294d560443d76d201fe01588eace  DriftLean.tar.xz' | sha256sum -c -
tar -xJf DriftLean.tar.xz
cp "$here/certificate.py" "$here/evaluator.py" .
base64 -d "$here/../agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -dc > Boundary.lean
export LEAN_PATH="$tmp"
python3 generate_exit.py
python3 generate_bellman_packed.py
python3 generate_vcheck.py
for m in Boundary DriftCore DriftRelations DriftExit DriftMacro DriftBellman DriftSource DriftXData DriftXCheck DriftVPacked; do
  lean -o "$m.olean" "$m.lean"
done
for i in 0 1 2 3 4; do
  lean -o "DriftVCheck$i.olean" "DriftVCheck$i.lean"
done
lean -o DriftVCheck.olean DriftVCheck.lean

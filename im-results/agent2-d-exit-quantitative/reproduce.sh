#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
base64 -d "$here/d-exit-quant.tar.xz.b64" > "$work/proof.tar.xz"
echo "96f20984c57f4f44903c86eae7c2c1e7ecd3af091747222fe24ff6271bd20397  $work/proof.tar.xz" | sha256sum -c -
tar -xJf "$work/proof.tar.xz" -C "$work"
base64 -d "$root/im-results/agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > "$work/Boundary.lean"
echo "0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  $work/Boundary.lean" | sha256sum -c -
cd "$work"
export LEAN_PATH="$work"
python3 certificate.py
python3 generate.py > Concrete.lean
for m in Boundary CostTree FiniteCheck Concrete ExitSound Evaluator SourceBridge Space Displacement; do
  lean -o "$m.olean" "$m.lean" 2>&1 | tee "$m.log"
  if grep -E 'sorryAx|uses .sorry.' "$m.log"; then exit 1; fi
done

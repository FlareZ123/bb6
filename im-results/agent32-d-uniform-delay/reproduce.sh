#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
D="$(mktemp -d)"
trap 'rm -rf "$D"' EXIT
base64 -d "$ROOT/im-results/agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > "$D/Boundary.lean"
base64 -d "$ROOT/im-results/agent25-cryptid-doublezero/TripleUniversal.lean.xz.b64" | xz -d > "$D/TripleUniversal.lean"
base64 -d "$ROOT/im-results/agent32-d-uniform-delay/UniformDelay.lean.xz.b64" | xz -d > "$D/UniformDelay.lean"
for m in DoubleZero TripleUniversalBase TripleUniversalCore TripleUniversalWalk TenPump TokenCode; do
  cp "$ROOT/im-results/agent25-cryptid-doublezero/$m.lean" "$D/"
done
cp "$ROOT/im-results/agent35-cryptid-code/ABridgeCode.lean" "$D/"
cp "$ROOT/im-results/agent32-cryptid-third/CryptidSix.lean" "$ROOT/im-results/agent32-cryptid-third/CryptidTriplePairs.lean" "$D/"
python3 - "$D/ABridgeCode.lean" <<'PY'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
s = p.read_text()
s = s.replace("| zero => cases h <;> rfl", "| zero => cases h <;> cases l <;> rfl")
s = s.replace("| succ st => cases h <;> simp [toA, CryptidBoundary.step, CryptidA.step]", "| succ st => cases st <;> cases h <;> rfl")
p.write_text(s)
PY
cd "$D"
echo '3bab7049c8b57e8f66b03f4b22d0792263c25755f01a191112250308f7fa5a2e  UniformDelay.lean' | sha256sum -c
export LEAN_PATH="$D"
for m in Boundary DoubleZero TripleUniversalBase TripleUniversalCore TripleUniversalWalk TripleUniversal TenPump TokenCode ABridgeCode CryptidSix CryptidTriplePairs; do
  lean -o "$m.olean" "$m.lean"
done
lean UniformDelay.lean

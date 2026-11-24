#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cd "$work"
base64 -d "$here/first-proof.tar.xz.b64" > first-proof.tar.xz
cat "$here"/guard-src.part{00,01,02} | base64 -d > guard-src.tar.xz
base64 -d "$here/../agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > Boundary.lean
sha256sum -c <<'EOF'
413d8ce714150271d518144b1a3387ca7f763798facdec16b5fe4bea5a7ebd52  first-proof.tar.xz
728f21dee8804e007e5abb269fbd3add1e6f731e328a7a247068a8c58343966b  guard-src.tar.xz
0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  Boundary.lean
EOF
tar -xJf first-proof.tar.xz
tar -xJf guard-src.tar.xz
python3 generate.py > GuardData.lean
python3 gen_guard_rank.py > GuardRankData.lean
sha256sum -c <<'EOF'
e93f132d263855e09048bce46108c6dd87d26bb9acdb4ca192f9f0fd7885ae0f  GuardData.lean
bf446aff633084137e09c7d36365ddc49f40723442bc0e913b9a3feb6a96d782  GuardRankData.lean
EOF
export LEAN_PATH=.
for m in Boundary ExitCore LowerData LowerRank RawExit RankWidth GuardData GuardBase GuardChecks GuardRest GuardRankData GuardRank SourceAdapter GuardSource EReturnSource; do
  lean -o "$m.olean" "$m.lean" 2>&1 | tee "$m.log"
  if grep -Eq 'sorryAx|uses .sorry.|native_decide' "$m.log"; then exit 1; fi
done
cp "$here/bounded_inverse.py" .
python3 bounded_inverse.py

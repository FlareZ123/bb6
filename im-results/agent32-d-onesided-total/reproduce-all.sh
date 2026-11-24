#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
here="$root/im-results/agent32-d-onesided-total"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cd "$work"
base64 -d "$here/OneSided.tar.xz.b64" > OneSided.tar.xz
echo 'c11d6e571c5bdd2c963a65b3bd34fecfec1d65cf52d6b79b4ada7c3195ee4c40  OneSided.tar.xz' | sha256sum -c
tar -xJf OneSided.tar.xz
base64 -d "$here/OneSidedE.tar.xz.b64" > OneSidedE.tar.xz
echo '9aed35c1ae1fc7bb34738812c2a4bb8885ac6f16d3844537ad12e30b80339228  OneSidedE.tar.xz' | sha256sum -c
tar -xJf OneSidedE.tar.xz
cat "$here"/OneSidedAll.b64.part{00,01,02} | base64 -d > OneSidedAll.tar.xz
echo '06286109fd7afbfa611f23a551bc0fc8d774bdfde18481aa666310e77cf9caa8  OneSidedAll.tar.xz' | sha256sum -c
tar -xJf OneSidedAll.tar.xz
base64 -d "$root/im-results/agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > Boundary.lean
base64 -d "$root/im-results/agent25-e-seam-kernel/SourceSeamFrame.lean.xz.b64" | xz -d > SourceSeamFrame.lean
cp "$root/im-results/agent31-d-exceptional/ESeamSource.lean" .
echo '0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  Boundary.lean' | sha256sum -c
export LEAN_PATH="$work"
lean --version
for mod in Boundary ESeamSource SourceSeamFrame OneSidedRank OneSidedCertificate OneSidedBounds OneSidedSource OneSidedTotal OneSidedECompletion OneSidedRefined OneSidedRefinedCert OneSidedRefinedTotal OneSidedAPairs OneSidedABlank OneSidedABlankTotal OneSidedSectorWalk OneSidedSectorTotal OneSidedFAll; do
  echo "Checking $mod"
  lean -o "$mod.olean" "$mod.lean" 2>&1 | tee "$mod.log"
  if grep -Eq 'sorryAx|uses .sorry.|declaration uses .sorry.' "$mod.log"; then exit 1; fi
done
grep -F "'BB6.OneSided.every_prepared_F_first' depends on axioms: [propext, Classical.choice, Quot.sound]" OneSidedFAll.log

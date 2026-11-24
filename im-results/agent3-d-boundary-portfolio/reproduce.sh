#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cd "$work"
base64 -d "$here/../agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > Boundary.lean
echo '0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  Boundary.lean' | sha256sum -c
cp "$here/../agent31-cryptid-boundary/BoundaryExtra.lean" .
cp "$here/../agent3-portfolio-raw-conjugacy/"{MachineConjugacy,DTableWitness}.lean .
cp "$here/../agent36-cryptid-trace/"{DAllBlankSource,DAllBlankHalting}.lean .
cp "$here/"{BoundaryPortfolio,DRootTransfer}.lean .
export LEAN_PATH="$PWD"
lean --version
for mod in Boundary MachineConjugacy DTableWitness BoundaryExtra DAllBlankSource DAllBlankHalting BoundaryPortfolio DRootTransfer; do
  lean -o "$mod.olean" "$mod.lean" 2>&1 | tee "$mod.log"
  if grep -Eq 'sorryAx|native_decide|uses .sorry.' "$mod.log"; then exit 1; fi
done

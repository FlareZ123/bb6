#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$here/w7-build}"
mkdir -p "$out"
out="$(cd "$out" && pwd)"
for archive in physical-source affine-source checker-source; do
  tar -xzf "$here/$archive.tar.gz" -C "$out"
done
cp "$here/../agent29-roster-six-audit/Row146Conjugacy.lean" "$out/"
cp "$here/W7Native.lean" "$out/"
cd "$out"
export LEAN_PATH="$out"
for mod in Row146Conjugacy W7Local W7Stack W7Sweep W7Affine W7Table W7Symbolic W7Difference W7Checker W7IO W7Roots W7Path W7Text; do
  lean -o "$mod.olean" "$out/$mod.lean"
done
if [[ "${W7_EXPORT:-0}" == 1 ]]; then
  python3 "$here/export_certs.py" --out "$out" N A Q D E Dentry
fi
if [[ "${W7_CHECK:-0}" == 1 ]]; then
  lean --run "$out/W7IO.lean" N A Q D E Dentry
  lean -o W7Native.olean "$out/W7Native.lean"
fi

#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo_root="$(cd "$here/../.." && pwd)"
inherited_lean_path="${LEAN_PATH:-}"
absolute_inherited_lean_path=""
IFS=':' read -r -a inherited_lean_dirs <<< "$inherited_lean_path"
for inherited_lean_dir in "${inherited_lean_dirs[@]}"; do
  [[ -n "$inherited_lean_dir" ]] || continue
  if [[ "$inherited_lean_dir" = /* ]]; then
    resolved_lean_dir="$inherited_lean_dir"
  else
    resolved_lean_dir="$repo_root/$inherited_lean_dir"
  fi
  absolute_inherited_lean_path="${absolute_inherited_lean_path:+$absolute_inherited_lean_path:}$resolved_lean_dir"
done
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cd "$work"
base64 -d "$here/../agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > Boundary.lean
base64 -d "$here/../agent32-d-onesided-total/OneSided.tar.xz.b64" > OneSided.tar.xz
base64 -d "$here/../agent32-d-route-dag/guard-source.tar.xz.b64" > guard.tar.xz
base64 -d "$here/growth.tar.xz.b64" > growth.tar.xz
sha256sum -c <<'CHECK'
0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  Boundary.lean
c11d6e571c5bdd2c963a65b3bd34fecfec1d65cf52d6b79b4ada7c3195ee4c40  OneSided.tar.xz
f5d6941c80576e05dfd37c05e2bd500cf584e9c26cc01152141d243b25211d80  guard.tar.xz
7d31e9bcdcf31e13497a7acf2df6d9fe1d5d5f7e4494f54e3c62561f0081c560  growth.tar.xz
CHECK
for a in OneSided guard growth; do tar -xJf "$a.tar.xz"; done
python3 split_guard9.py
sed -i '/import RouteAllFront/d; s/open CryptidBoundary BB6.Agent32Route/open CryptidBoundary/' Guarded9Macro.lean
export LEAN_PATH="$PWD"
for mod in Boundary OneSidedRank OneSidedCertificate OneSidedBounds OneSidedSource OneSidedTotal RankGrowth Guard9 Guard9Cert Guard9Total Guarded9Macro GuardGrowth GrowthMacro SectionBands; do
  lean -o "$mod.olean" "$mod.lean" 2>&1 | tee "$mod.log"
  if grep -Eq 'sorryAx|uses .sorry.' "$mod.log"; then exit 1; fi
done

if [[ -n "${EXTRA_MODULES:-}" ]]; then
  # Extra modules may import source theorems compiled in the workflow's
  # repository directories.  Preserve the caller's search path after
  # resolving its relative entries against the repository root: this
  # script compiles in a temporary directory, so relative paths otherwise
  # silently point at the wrong place.
  export LEAN_PATH="$PWD:$here/../agent26-d-phase-bands:$here/../agent36-cryptid-trace:$absolute_inherited_lean_path"
  IFS=',' read -ra extra_modules <<< "$EXTRA_MODULES"
  for extra_module in "${extra_modules[@]}"; do
    cp "$here/../agent36-cryptid-trace/$extra_module" "$work/$extra_module"
    extra_olean="${extra_module%.lean}.olean"
    extra_log="${extra_module%.lean}.log"
    lean -o "$extra_olean" "$extra_module" 2>&1 | tee "$extra_log"
    if grep -Eq 'sorryAx|uses .sorry.' "$extra_log"; then exit 1; fi
  done
fi

if [[ "${SHOW_SECTION_BANDS:-0}" == "1" ]]; then
  echo "=== GrowthMacro key declarations ==="
  grep -nE '^(namespace|def |abbrev |structure |theorem |lemma )' GrowthMacro.lean
  echo "=== GrowthMacro source ==="
  sed -n '1,180p' GrowthMacro.lean
  echo "=== SectionBands public declarations ==="
  grep -nE '^(namespace|open |def |abbrev |structure |theorem |lemma )' SectionBands.lean
  echo "=== SectionBands source ==="
  sed -n '1,260p' SectionBands.lean
fi

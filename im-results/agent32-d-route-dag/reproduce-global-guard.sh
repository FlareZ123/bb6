#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cd "$work"
for a in route-proof route-block-lean counted-blocks counted-source; do
  base64 -d "$here/$a.tar.xz.b64" > "$a.tar.xz"
done
echo '8541613dfcd228fed738f28def38ba759ec7e9002f6b7f741b74a9592f86a4c3  route-proof.tar.xz
3b96983829a6da14cbdfd0db93216031d9891227b81467a84f742b3124cc7c3b  route-block-lean.tar.xz
f789c7348e3b3e0a4a014c475b7d05ed92911c7e9da3ba568ff7bdc6beda9c7c  counted-blocks.tar.xz
93b8a03168cb877bbc732c34230163433e4ca8f71ad87bd240c6888fd8a7f945  counted-source.tar.xz' | sha256sum -c
for a in route-proof route-block-lean counted-blocks counted-source; do tar -xJf "$a.tar.xz"; done
base64 -d "$here/../agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > Boundary.lean
echo '0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883  Boundary.lean' | sha256sum -c
cp "$here/../agent32-cryptid-padding/Generic.lean" "$here/../agent32-cryptid-padding/BoundaryPadding.lean" .
cp "$here/RouteMembership.lean" RouteMembership.full.lean
# Exact dependency projection: copy only the two declarations needed by the
# block/source modules, avoiding recompilation of the unrelated giant DAG.
python3 - <<'PY'
from pathlib import Path
g=Path('RouteGraphChunks.lean').read_text()
m=Path('RouteMembership.full.lean').read_text()
a=g.index('def Halts (')
b=g.index('\n',a)
x=m.index('theorem root_section_halts ')
y=m.index('\n#print axioms',x)
Path('RouteMembership.lean').write_text(
    'import RouteFront\nnamespace BB6.Agent32Route\nopen CryptidBoundary BB6.Padding BB6.BoundaryPadding\n'
    +g[a:b]+'\n\n'+m[x:y]+'\nend BB6.Agent32Route\n')
PY
export LEAN_PATH="$PWD"
for mod in Boundary Generic BoundaryPadding RouteFront RouteMembership RouteTokens RouteAllFront RouteBlock RoutePartial RouteReplayExact RouteHalt CountedBlocks CountedReplay CountedSource; do
  lean -o "$mod.olean" "$mod.lean" 2>&1 | tee "$mod.log"
  if grep -Eq 'sorryAx|uses .sorry.' "$mod.log"; then exit 1; fi
done
# Reuse the prior well-founded rank proof and the generator's reference template.
old="$here/../agent32-d-onesided-total"
base64 -d "$old/OneSided.tar.xz.b64" > OneSided.tar.xz
cat "$old"/OneSidedAll.b64.part{00,01,02} | base64 -d > OneSidedAll.tar.xz
base64 -d "$here/guard-source.tar.xz.b64" > guard-source.tar.xz
echo 'c11d6e571c5bdd2c963a65b3bd34fecfec1d65cf52d6b79b4ada7c3195ee4c40  OneSided.tar.xz
06286109fd7afbfa611f23a551bc0fc8d774bdfde18481aa666310e77cf9caa8  OneSidedAll.tar.xz
f5d6941c80576e05dfd37c05e2bd500cf584e9c26cc01152141d243b25211d80  guard-source.tar.xz' | sha256sum -c
for a in OneSided OneSidedAll guard-source; do tar -xJf "$a.tar.xz"; done
python3 split_guard9.py
echo 'b8af28fd6aa90a6368c4ea7e215d451dd44372fe7115696eafe0bfcfcca7f204  Guard9Cert.lean' | sha256sum -c
for mod in OneSidedRank OneSidedCertificate OneSidedBounds OneSidedSource OneSidedTotal Guard9 Guard9Cert Guard9Total Guarded9Macro Guard9Sound AllGuard TotalAffine; do
  lean -o "$mod.olean" "$mod.lean" 2>&1 | tee "$mod.log"
  if grep -Eq 'sorryAx|uses .sorry.' "$mod.log"; then exit 1; fi
done

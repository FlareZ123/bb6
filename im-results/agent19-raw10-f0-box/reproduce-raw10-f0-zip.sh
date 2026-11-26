#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
UPSTREAM_ROOT="${UPSTREAM_ROOT:?set UPSTREAM_ROOT to the pinned Cryptids checkout}"
WORKDIR="${WORKDIR:-/tmp/agent19-raw10-f0-zip}"
JOBS="${JOBS:-4}"
LEAN_BIN="${LEAN_BIN:-$HOME/.elan/bin/lean}"
PINNED="3647718b5df22e1a61462dec0376bd204526285a"
export UPSTREAM_ROOT LEAN_BIN

test -d "$UPSTREAM_ROOT"
test "$(git -C "$UPSTREAM_ROOT" rev-parse HEAD)" = "$PINNED"
test -s "$UPSTREAM_ROOT/.lake/build/lib/lean/BusyBeaver/Basic.olean"
test -s "$UPSTREAM_ROOT/.lake/build/lib/lean/BusyBeaver/Calculi/CtlCertificate.olean"
test -s "$UPSTREAM_ROOT/.lake/build/lib/lean/BusyBeaver/BB6/NonHalt/M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH.olean"
test -s "$UPSTREAM_ROOT/.lake/build/lib/lean/BusyBeaver/BB6/NonHalt/M_1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA.olean"

python3 "$ROOT/tools/test_lean_compile_module_index.py"
mkdir -p "$WORKDIR"
python3 - "$ROOT" "$WORKDIR" <<'PY'
import base64
import hashlib
import lzma
from pathlib import Path
import sys

root, work = Path(sys.argv[1]), Path(sys.argv[2])
encoded = root / "im-results/agent13-coverage/BB6Coverage.lean.xz.b64"
source = lzma.decompress(base64.b64decode(encoded.read_bytes()))
digest = hashlib.sha256(source).hexdigest()
expected = "fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd"
if digest != expected:
    raise SystemExit(f"BB6Coverage source checksum mismatch: {digest}")
target = work / "BB6Coverage.lean"
target.write_bytes(source)
(work / "BB6Coverage.sha256").write_text(digest + "  BB6Coverage.lean\n", encoding="utf-8")
print(f"Materialized pinned BB6Coverage source: sha256={digest}")
PY
test -s "$WORKDIR/BB6Coverage.lean"
printf '%s\n' "$PINNED" > "$WORKDIR/upstream-commit.txt"
cp "$UPSTREAM_ROOT/lakefile.toml" "$WORKDIR/upstream-lakefile.toml"
cp "$UPSTREAM_ROOT/lake-manifest.json" "$WORKDIR/upstream-lake-manifest.json"
(cd "$WORKDIR" && sha256sum upstream-lakefile.toml upstream-lake-manifest.json > upstream-dependencies.sha256)

cat > "$WORKDIR/lean-with-upstream" <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
UPSTREAM_ROOT="${UPSTREAM_ROOT:?}"
LEAN_BIN="${LEAN_BIN:?}"
UPSTREAM_LEAN_PATH="$(cd "$UPSTREAM_ROOT" && lake env printenv LEAN_PATH)"
UPSTREAM_LIB="$UPSTREAM_ROOT/.lake/build/lib/lean"
test -s "$UPSTREAM_LIB/BusyBeaver/Basic.olean"
test -s "$UPSTREAM_LIB/BusyBeaver/Calculi/CtlCertificate.olean"
export LEAN_PATH="${LEAN_PATH:+$LEAN_PATH:}$UPSTREAM_LIB${UPSTREAM_LEAN_PATH:+:$UPSTREAM_LEAN_PATH}"
SOURCE="${@: -1}"
if [[ -f "$UPSTREAM_ROOT/$SOURCE" ]]; then cd "$UPSTREAM_ROOT"; fi
exec "$LEAN_BIN" "$@"
WRAPPER
chmod +x "$WORKDIR/lean-with-upstream"

python3 "$ROOT/tools/lean_compile_closure.py" \
  "$ROOT/im-results/agent19-raw10-f0-box/Raw10F0ZipCycles.lean" \
  --workdir "$WORKDIR/build" --source-root "$UPSTREAM_ROOT" --jobs "$JOBS" \
  --lean "$WORKDIR/lean-with-upstream" --manifest "$WORKDIR/build/manifest.json" \
  --label raw10-f0-zipcycle-box-minimal-source-closure \
  --provenance-input "$WORKDIR/upstream-commit.txt" \
  --provenance-input "$WORKDIR/upstream-dependencies.sha256" \
  --provenance-input "$ROOT/im-results/agent19-raw10-f0-box/Raw10F0ZipCycles.lean" \
  --provenance-input "$ROOT/im-results/agent19-raw10-f0-box/search_zipcycles.js" \
  --provenance-input "$ROOT/im-results/agent19-raw10-f0-box/README.md" \
  --provenance-input "$ROOT/im-results/agent13-block-far/Raw10FixedLeaves.lean" \
  --provenance-input "$ROOT/im-results/agent10-tnf-multipump/ZipAuditCore.lean" \
  --provenance-input "$ROOT/im-results/agent13-weighted-first-one/WeightedFirstOneCover.lean" \
  --override Raw10CtlFootprint=im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprint.lean \
  --override Raw10CtlFootprintSecond=im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprintSecond.lean \
  --override Raw10CtlDualConsumer=im-results/agent50-weighted-tnf-pilot/Raw10CtlDualConsumer.lean \
  --override Raw10BoxCore=im-results/agent49-box-complement/Raw10BoxCore.lean \
  --override Raw10FixedLeaves=im-results/agent13-block-far/Raw10FixedLeaves.lean \
  --override Raw10F0ZipCycles=im-results/agent19-raw10-f0-box/Raw10F0ZipCycles.lean \
  --override BB6Coverage=.tmp/agent50-raw10-ctl-footprint/BB6Coverage.lean \
  --override BoxComplement=im-results/agent49-box-complement/BoxComplement.lean \
  --override RootRaw10Core=im-results/agent13-cross-route-pilot/RootRaw10Core.lean \
  --override CrossRouteHeldLeaf=im-results/agent13-cross-route-pilot/CrossRouteHeldLeaf.lean \
  --override SideWitnessCore=im-results/agent47-rooted-tnf/SideWitnessCore.lean \
  --override RootFrontier=im-results/agent50-weighted-tnf-pilot/RootFrontier.lean \
  --override TNFPilot=im-results/agent50-weighted-tnf-pilot/TNFPilot.lean \
  --override SideCycle=im-results/agent50-weighted-tnf-pilot/SideCycle.lean \
  --override AlternatingResidualSweep=im-results/agent50-weighted-tnf-pilot/AlternatingResidualSweep.lean \
  --override AlternatingVariants=im-results/agent50-weighted-tnf-pilot/AlternatingVariants.lean \
  --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
  --override FirstHolePath=im-results/agent8-cryptids-tnf-paths/FirstHolePath.lean \
  --override CryptidsFirstHolePaths=im-results/agent8-cryptids-tnf-paths/CryptidsFirstHolePaths.lean \
  --override FiniteLassoOracle=im-results/agent32-zero-prefix-global/FiniteLassoOracle.lean \
  --override RayFiniteOracle=im-results/agent8-coverage-contract/RayFiniteOracle.lean \
  --override RayFinite=im-results/agent8-coverage-contract/RayFinite.lean \
  --override RayEntry=im-results/agent8-coverage-contract/RayEntry.lean \
  --override RayChecker=im-results/agent8-coverage-contract/RayChecker.lean \
  --override RayTurnExample=im-results/agent8-coverage-contract/RayTurnExample.lean \
  --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
  --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
  --override Prune=im-results/agent8-coverage-contract/Prune.lean \
  --override OneHalt=im-results/agent8-coverage-contract/OneHalt.lean \
  --override FirstStep=im-results/agent42-coverage-normal/FirstStep.lean \
  --override TwoFirst=im-results/agent42-coverage-normal/TwoFirst.lean \
  --override WriteOneDrift=im-results/agent4-coverage-smoke/WriteOneDrift.lean \
  --override CrossCoverage=im-results/agent4-coverage-smoke/CrossCoverage.lean \
  --override CrossUpper=im-results/agent4-coverage-smoke/CrossUpper.lean \
  --override CrossFirstUpper=im-results/agent42-coverage-normal/CrossFirstUpper.lean \
  --override TwoCylinder=im-results/agent42-coverage-normal/TwoCylinder.lean \
  --override BlankDelayKernel=im-results/agent13-weighted-first-one/BlankDelayKernel.lean \
  --override BlankDelaySource=im-results/agent13-weighted-first-one/BlankDelaySource.lean \
  --override SparseBlankDelay=im-results/agent13-weighted-first-one/SparseBlankDelay.lean \
  --override WeightedTNF=im-results/agent13-weighted-first-one/WeightedTNF.lean \
  --override WeightedTNFCertificate=im-results/agent13-weighted-first-one/WeightedTNFCertificate.lean \
  --override WeightedFirstOneCover=im-results/agent13-weighted-first-one/WeightedFirstOneCover.lean \
  --override ZipPrefixAudit=im-results/agent48-prefix-audit/ZipPrefixAudit.lean \
  --override ZipThreeHoleAudit=im-results/agent10-tnf-multipump/ZipThreeHoleAudit.lean \
  --override ZipAuditCore=im-results/agent10-tnf-multipump/ZipAuditCore.lean \
  --override ThreeHoleAudit=im-results/agent31-three-hole-tnf/ThreeHoleAudit.lean \
  --override SweepPumping=im-results/agent31-three-hole-tnf/SweepPumping.lean \
  --override FastFAR=im-results/agent7-far/FastFAR.lean \
  --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
  --override RelativeTape=im-results/agent4-coverage-smoke/RelativeTape.lean \
  --override CryptidsTapeAdapter=im-results/agent4-coverage-smoke/CryptidsTapeAdapter.lean \
  2>&1 | tee "$WORKDIR/compile.log"

python3 - "$WORKDIR/compile.log" "$WORKDIR/build/manifest.json" "$WORKDIR/axiom-summary.json" <<'PY'
import json, pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
manifest = json.loads(pathlib.Path(sys.argv[2]).read_text())
profiles = {
    name: {x.strip() for x in raw.split(",") if x.strip()}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \\[([^\\]]*)\\]", log)
}
required = [
    "BB6.Agent19Raw10F0Box.raw10F0ZipLeaves",
    "BB6.Agent19Raw10F0Box.raw10F0F1ZipLeaves",
    "BB6.Agent19Raw10F0Box.raw10HaltCovers",
    "BB6.Agent19Raw10F0Box.f0Domain_partition",
    "BB6.Agent19Raw10F0Box.branchPair_partition",
    "BB6.Agent19Raw10F0Box.raw10Box_total_count",
    "BB6.Agent19Raw10F0Box.raw10NonhaltCount",
    "BB6.Agent19Raw10F0Box.raw10ObservedHaltCount",
    "BB6.Agent19Raw10F0Box.raw10OpenCount",
    "BB6.Agent19Raw10F0Box.raw10Partition_count",
]
allowed = {"propext", "Classical.choice", "Quot.sound"}
missing = [name for name in required if name not in profiles]
if missing:
    raise SystemExit("missing required axiom profiles: " + ", ".join(missing))
bad = {name: sorted(profiles[name] - allowed) for name in required if profiles[name] - allowed}
if bad:
    raise SystemExit("unexpected theorem axioms: " + json.dumps(bad, sort_keys=True))
if "sorryAx" in log or "native_decide" in log:
    raise SystemExit("forbidden sorryAx/native_decide marker in compilation log")
summary = {
    "claim": "partial proof-carrying decomposition of one 575-completion Raw10 two-hole residual box; not a full parent cover",
    "fixed_prefix": "1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD",
    "f0_domain_size": 23,
    "f1_domain_size": 25,
    "residual_box_completions": 575,
    "nonhalting_completions": 490,
    "halting_completions": 28,
    "open_completions": 57,
    "module_count": manifest["module_count"],
    "theorem_axioms": {name: sorted(profiles[name]) for name in required},
}
pathlib.Path(sys.argv[3]).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\\n")
print(json.dumps(summary, indent=2, sort_keys=True))
PY

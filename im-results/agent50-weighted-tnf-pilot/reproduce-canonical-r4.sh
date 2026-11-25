#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
CANONICAL77_DIR="${CANONICAL77_DIR:?set CANONICAL77_DIR to the extracted canonical77-certified artifact}"
CANONICAL77_MANIFEST="${CANONICAL77_MANIFEST:?set CANONICAL77_MANIFEST to canonical77-base-manifest.json}"
UPSTREAM_ROOT="${UPSTREAM_ROOT:?set UPSTREAM_ROOT to the pinned Cryptids checkout}"
WORKDIR="${WORKDIR:-/tmp/agent50-canonical-r4}"
JOBS="${JOBS:-4}"
LEAN_BIN="${LEAN_BIN:-$HOME/.elan/bin/lean}"
export UPSTREAM_ROOT LEAN_BIN

test -s "$CANONICAL77_DIR/CanonicalRaw114Accepted.olean"
test -s "$CANONICAL77_DIR/CanonicalTwoParentGraft.olean"
test -s "$CANONICAL77_MANIFEST"
test -d "$UPSTREAM_ROOT"

mkdir -p "$WORKDIR"
printf '%s\n' "$(git -C "$UPSTREAM_ROOT" rev-parse HEAD)" > "$WORKDIR/upstream-commit.txt"

cat > "$WORKDIR/lean-with-upstream" <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
UPSTREAM_ROOT="${UPSTREAM_ROOT:?}"
LEAN_BIN="${LEAN_BIN:?}"
UPSTREAM_LEAN_PATH="$(cd "$UPSTREAM_ROOT" && lake env printenv LEAN_PATH)"
export LEAN_PATH="${LEAN_PATH:+$LEAN_PATH:}$UPSTREAM_LEAN_PATH"
exec "$LEAN_BIN" "$@"
WRAPPER
chmod +x "$WORKDIR/lean-with-upstream"

python3 "$ROOT/tools/lean_compile_closure.py" \
  "$ROOT/im-results/agent50-weighted-tnf-pilot/CanonicalR4Ingestion.lean" \
  --workdir "$WORKDIR/build" \
  --source-root "$UPSTREAM_ROOT" \
  --jobs "$JOBS" \
  --lean "$WORKDIR/lean-with-upstream" \
  --precompiled-manifest "$CANONICAL77_MANIFEST" \
  --precompiled-dir "$CANONICAL77_DIR" \
  --manifest "$WORKDIR/build/manifest.json" \
  --label canonical-r4-ingestion \
  --provenance-input "$WORKDIR/upstream-commit.txt" \
  --provenance-input "$CANONICAL77_MANIFEST" \
  --override RootFrontier=im-results/agent50-weighted-tnf-pilot/RootFrontier.lean \
  --override TNFPilot=im-results/agent50-weighted-tnf-pilot/TNFPilot.lean \
  --override SideCycle=im-results/agent50-weighted-tnf-pilot/SideCycle.lean \
  --override AlternatingResidualSweep=im-results/agent50-weighted-tnf-pilot/AlternatingResidualSweep.lean \
  --override AlternatingVariants=im-results/agent50-weighted-tnf-pilot/AlternatingVariants.lean \
  --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
  --override RootFrontierR1R4=im-results/agent47-rooted-tnf/RootFrontierR1R4.lean \
  --override R1Graft=im-results/agent47-r1-sweep/R1Graft.lean \
  --override R1Parent=im-results/agent47-r1-sweep/R1Parent.lean \
  --override R1RF=im-results/agent47-r1-sweep/R1RF.lean \
  --override R1Certificate=im-results/agent47-r1-sweep/R1Certificate.lean \
  --override R4Graft=im-results/agent47-r4-counter/R4Graft.lean \
  --override R4Parent=im-results/agent47-r4-counter/R4Parent.lean \
  --override R4Counter=im-results/agent47-r4-counter/R4Counter.lean \
  --override Cryptids608NonHalt=im-results/agent42-cryptids-current-main/Cryptids608NonHalt.lean \
  --override CryptidsWeightedLeaves=im-results/agent47-weighted-halt-branch/CryptidsWeightedLeaves.lean \
  --override WeightedNonhaltLeafAdapter=im-results/agent47-weighted-halt-branch/WeightedNonhaltLeafAdapter.lean \
  --override HardRootCore=im-results/agent19-hard-root-crosswalk/HardRootCore.lean \
  --override HardRootParents=im-results/agent19-hard-root-crosswalk/HardRootParents.lean \
  --override CanonicalRosterRefinement=im-results/agent47-rooted-tnf/CanonicalRosterRefinement.lean \
  --override CanonicalRaw114Accepted=im-results/agent47-rooted-tnf/CanonicalRaw114Accepted.lean \
  --override CanonicalFrontier=im-results/agent47-rooted-tnf/CanonicalFrontier.lean \
  --override FirstHolePath=im-results/agent8-cryptids-tnf-paths/FirstHolePath.lean \
  --override CryptidsFirstHolePaths=im-results/agent8-cryptids-tnf-paths/CryptidsFirstHolePaths.lean \
  --override FiniteLassoOracle=im-results/agent32-zero-prefix-global/FiniteLassoOracle.lean \
  --override PhysicalTraceAudit=im-results/agent32-zero-prefix-global/PhysicalTraceAudit.lean \
  --override RayFiniteOracle=im-results/agent8-coverage-contract/RayFiniteOracle.lean \
  --override RayFinite=im-results/agent8-coverage-contract/RayFinite.lean \
  --override RayEntry=im-results/agent8-coverage-contract/RayEntry.lean \
  --override RayChecker=im-results/agent8-coverage-contract/RayChecker.lean \
  --override RayTurnExample=im-results/agent8-coverage-contract/RayTurnExample.lean \
  --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
  --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
  --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
  --override Prune=im-results/agent8-coverage-contract/Prune.lean \
  --override OneHalt=im-results/agent8-coverage-contract/OneHalt.lean \
  --override FirstStep=im-results/agent42-coverage-normal/FirstStep.lean \
  --override TwoFirst=im-results/agent42-coverage-normal/TwoFirst.lean \
  --override WriteOneDrift=im-results/agent4-coverage-smoke/WriteOneDrift.lean \
  --override CrossCoverage=im-results/agent4-coverage-smoke/CrossCoverage.lean \
  --override CrossUpper=im-results/agent4-coverage-smoke/CrossUpper.lean \
  --override CrossFirstUpper=im-results/agent42-coverage-normal/CrossFirstUpper.lean \
  --override TwoCylinder=im-results/agent42-coverage-normal/TwoCylinder.lean \
  --override BB6Coverage=im-results/agent13-coverage/BB6Coverage.lean \
  --override BlankDelayKernel=im-results/agent13-weighted-first-one/BlankDelayKernel.lean \
  --override BlankDelaySource=im-results/agent13-weighted-first-one/BlankDelaySource.lean \
  --override SparseBlankDelay=im-results/agent13-weighted-first-one/SparseBlankDelay.lean \
  --override WeightedTNF=im-results/agent13-weighted-first-one/WeightedTNF.lean \
  --override WeightedTNFCertificate=im-results/agent13-weighted-first-one/WeightedTNFCertificate.lean \
  --override WeightedFirstOneCover=im-results/agent13-weighted-first-one/WeightedFirstOneCover.lean \
  2>&1 | tee "$WORKDIR/compile.log"

if grep -Eq 'sorryAx|native_decide' "$WORKDIR/compile.log"; then
  echo "Forbidden proof placeholder or native_decide found in canonical r4 ingestion closure" >&2
  exit 1
fi

python3 - "$WORKDIR/compile.log" "$WORKDIR/build/manifest.json" <<'PY'
import json, pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
manifest = json.loads(pathlib.Path(sys.argv[2]).read_text())
profiles = {
    name: {x.strip() for x in raw.split(",") if x.strip()}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
}
required = [
    "BB6.Agent50CanonicalR4Ingestion.residuals_closed_expanded",
    "BB6.Agent50CanonicalR4Ingestion.r4Subtree",
    "BB6.Agent50CanonicalR4Ingestion.r4Remaining_sound",
    "BB6.Agent50CanonicalR4Ingestion.r4RefinedRoster_sound",
    "BB6.Agent50CanonicalR4Ingestion.r4_terminal_hole_count",
]
allowed = {"propext", "Classical.choice", "Quot.sound"}
missing = [name for name in required if name not in profiles]
if missing:
    raise SystemExit("missing required axiom profiles: " + ", ".join(missing))
bad = {name: sorted(profiles[name] - allowed) for name in required if profiles[name] - allowed}
if bad:
    raise SystemExit("unexpected theorem axioms: " + json.dumps(bad, sort_keys=True))
summary = {
    "claim": "canonical77 p23 is refined by the source-connected r4 first-hole subtree; 161 residual cylinders remain and the r4 terminal parent has 625 completions",
    "module_count": manifest["module_count"],
    "reused_precompiled_modules": manifest.get("precompiled_core", {}).get("reused_module_count", 0),
    "theorem_axioms": {name: sorted(profiles[name]) for name in required},
}
pathlib.Path(pathlib.Path(sys.argv[2]).parent / "axiom-summary.json").write_text(
    json.dumps(summary, indent=2, sort_keys=True) + "\n"
)
print(json.dumps(summary, indent=2, sort_keys=True))
PY

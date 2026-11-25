#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
CANONICAL77_DIR="${CANONICAL77_DIR:?set CANONICAL77_DIR to the extracted canonical77-certified artifact}"
CANONICAL77_MANIFEST="${CANONICAL77_MANIFEST:?set CANONICAL77_MANIFEST to canonical77-base-manifest.json}"
UPSTREAM_ROOT="${UPSTREAM_ROOT:?set UPSTREAM_ROOT to the pinned Cryptids checkout}"
WORKDIR="${WORKDIR:-/tmp/agent19-raw10-cryptids-leaf}"
JOBS="${JOBS:-4}"
LEAN_BIN="${LEAN_BIN:-$HOME/.elan/bin/lean}"
PINNED="3647718b5df22e1a61462dec0376bd204526285a"
export UPSTREAM_ROOT LEAN_BIN

test -s "$CANONICAL77_DIR/CanonicalRaw114Accepted.olean"
test -s "$CANONICAL77_DIR/CanonicalTwoParentGraft.olean"
test -s "$CANONICAL77_MANIFEST"
test -d "$UPSTREAM_ROOT"
test "$(git -C "$UPSTREAM_ROOT" rev-parse HEAD)" = "$PINNED"

python3 "$ROOT/tools/test_lean_compile_module_index.py"

mkdir -p "$WORKDIR"
printf '%s\n' "$PINNED" > "$WORKDIR/upstream-commit.txt"
# Record the exact local dependency overlay and fully resolved Lake lock.
cp "$UPSTREAM_ROOT/lakefile.toml" "$WORKDIR/upstream-lakefile.toml"
cp "$UPSTREAM_ROOT/lake-manifest.json" "$WORKDIR/upstream-lake-manifest.json"
(cd "$WORKDIR" && sha256sum upstream-lakefile.toml upstream-lake-manifest.json \
  > upstream-dependencies.sha256)

node "$ROOT/im-results/agent19-hard-root-crosswalk/raw10-cryptids-leaf-crosswalk.cjs" "$UPSTREAM_ROOT" \
  | tee "$WORKDIR/crosswalk.json"
sha256sum "$WORKDIR/crosswalk.json" > "$WORKDIR/crosswalk.sha256"

cat > "$WORKDIR/lean-with-upstream" <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
UPSTREAM_ROOT="${UPSTREAM_ROOT:?}"
LEAN_BIN="${LEAN_BIN:?}"
UPSTREAM_LEAN_PATH="$(cd "$UPSTREAM_ROOT" && lake env printenv LEAN_PATH)"
UPSTREAM_LIB="$UPSTREAM_ROOT/.lake/build/lib/lean"
test -s "$UPSTREAM_LIB/BusyBeaver/Basic.olean"
test -s "$UPSTREAM_LIB/Cryptids/Machines.olean"
export LEAN_PATH="${LEAN_PATH:+$LEAN_PATH:}$UPSTREAM_LIB${UPSTREAM_LEAN_PATH:+:$UPSTREAM_LEAN_PATH}"
# Upstream elaborators (e.g. load_machine_rows%) read data paths relative to
# the upstream project root. Local repository modules stay in the closure cwd.
SOURCE="${@: -1}"
if [[ -f "$UPSTREAM_ROOT/$SOURCE" ]]; then
  cd "$UPSTREAM_ROOT"
fi
exec "$LEAN_BIN" "$@"
WRAPPER
chmod +x "$WORKDIR/lean-with-upstream"

python3 "$ROOT/tools/lean_compile_closure.py" \
  "$ROOT/im-results/agent19-hard-root-crosswalk/Raw10CryptidsLeaf.lean" \
  --workdir "$WORKDIR/build" \
  --source-root "$UPSTREAM_ROOT" \
  --jobs "$JOBS" \
  --lean "$WORKDIR/lean-with-upstream" \
  --precompiled-manifest "$CANONICAL77_MANIFEST" \
  --precompiled-dir "$CANONICAL77_DIR" \
  --manifest "$WORKDIR/build/manifest.json" \
  --label raw10-cryptids-last-hole-leaf \
  --provenance-input "$WORKDIR/upstream-commit.txt" \
  --provenance-input "$WORKDIR/crosswalk.sha256" \
  --provenance-input "$WORKDIR/upstream-dependencies.sha256" \
  --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
  --override RootFrontier=im-results/agent50-weighted-tnf-pilot/RootFrontier.lean \
  --override TNFPilot=im-results/agent50-weighted-tnf-pilot/TNFPilot.lean \
  --override SideCycle=im-results/agent50-weighted-tnf-pilot/SideCycle.lean \
  --override AlternatingResidualSweep=im-results/agent50-weighted-tnf-pilot/AlternatingResidualSweep.lean \
  --override AlternatingVariants=im-results/agent50-weighted-tnf-pilot/AlternatingVariants.lean \
  --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
  --override RootFrontierR1R4=im-results/agent47-rooted-tnf/RootFrontierR1R4.lean \
  --override R1Graft=im-results/agent47-r1-sweep/R1Graft.lean \
  --override R1Parent=im-results/agent47-r1-sweep/R1Parent.lean \
  --override R1RB=im-results/agent47-r1-sweep/R1RB.lean \
  --override R1Pumps=im-results/agent47-r1-sweep/R1Pumps.lean \
  --override R1Sweep=im-results/agent47-r1-sweep/R1Sweep.lean \
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
  --override CanonicalTwoParentGraft=im-results/agent47-rooted-tnf/CanonicalTwoParentGraft.lean \
  --override Canonical78Roster=im-results/agent47-rooted-tnf/Canonical78Roster.lean \
  --override Combined106Roster=im-results/agent47-rooted-tnf/Combined106Roster.lean \
  --override FiveHoleRoster=im-results/agent10-tnf-multipump/FiveHoleRoster.lean \
  --override AllTwelveRoster=im-results/agent10-tnf-multipump/AllTwelveRoster.lean \
  --override NewFiveRoster=im-results/agent10-tnf-multipump/NewFiveRoster.lean \
  --override RosterCoverComposition=im-results/agent13-roster-convergence/RosterCoverComposition.lean \
  --override ZipPrefixAudit=im-results/agent48-prefix-audit/ZipPrefixAudit.lean \
  --override ZipThreeHoleAudit=im-results/agent10-tnf-multipump/ZipThreeHoleAudit.lean \
  --override ZipAuditCore=im-results/agent10-tnf-multipump/ZipAuditCore.lean \
  --override ThreeHoleAudit=im-results/agent31-three-hole-tnf/ThreeHoleAudit.lean \
  --override SweepPumping=im-results/agent31-three-hole-tnf/SweepPumping.lean \
  --override Raw114CompleteData=im-results/agent47-raw114-cut/Raw114CompleteData.lean \
  --override FourHoleResidualRoster=im-results/agent31-three-hole-tnf/FourHoleResidualRoster.lean \
  --override FourHoleRootFrontier=im-results/agent31-three-hole-tnf/FourHoleRootFrontier.lean \
  --override FourHoleData=im-results/agent31-three-hole-tnf/FourHoleData.lean \
  --override WeightedTNFQueueOrbit=im-results/agent13-weighted-first-one/WeightedTNFQueueOrbit.lean \
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
  --override Raw10HardRootR1Adapter=im-results/agent50-weighted-tnf-pilot/Raw10HardRootR1Adapter.lean \
  --override Raw10BoxCombinedConsumer=im-results/agent17-raw10-box-far-search/Raw10BoxCombinedConsumer.lean \
  --override Raw10Box8CycleConsumer=im-results/agent50-weighted-tnf-pilot/Raw10Box8CycleConsumer.lean \
  --override Raw10Box8Cycle=im-results/agent50-weighted-tnf-pilot/Raw10Box8Cycle.lean \
  --override Raw10Box0Halt=im-results/agent50-weighted-tnf-pilot/Raw10Box0Halt.lean \
  --override Raw10BoxBridge=im-results/agent49-box-complement/Raw10BoxBridge.lean \
  --override Raw10BoxCore=im-results/agent49-box-complement/Raw10BoxCore.lean \
  --override BoxComplement=im-results/agent49-box-complement/BoxComplement.lean \
  --override RootRaw10Core=im-results/agent13-cross-route-pilot/RootRaw10Core.lean \
  --override Root109Membership=im-results/agent13-cross-route-pilot/Root109Membership.lean \
  --override LeafRules=im-results/agent8-coverage-contract/LeafRules.lean \
  --override HardRootLeaves=im-results/agent19-hard-root-crosswalk/HardRootLeaves.lean \
  --override CryptidsTapeAdapter=im-results/agent4-coverage-smoke/CryptidsTapeAdapter.lean \
  --override RelativeTape=im-results/agent4-coverage-smoke/RelativeTape.lean \
  2>&1 | tee "$WORKDIR/compile.log"

python3 - "$WORKDIR/compile.log" "$WORKDIR/build/manifest.json" "$WORKDIR/axiom-summary.json" <<'PY'
import json, pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
manifest = json.loads(pathlib.Path(sys.argv[2]).read_text())
profiles = {
    name: {x.strip() for x in raw.split(",") if x.strip()}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
}
required = [
    "BB6.Agent19Raw10CryptidsLeaf.original_eq_candidate",
    "BB6.Agent19Raw10CryptidsLeaf.original_never",
    "BB6.Agent19Raw10CryptidsLeaf.candidate_never",
    "BB6.Agent19Raw10CryptidsLeaf.candidate_first_hole_path",
    "BB6.Agent19Raw10CryptidsLeaf.candidateWeightedLeaf",
    "BB6.Agent19Raw10CryptidsLeaf.candidateLeaf_box0_contains",
    "BB6.Agent19Raw10CryptidsLeaf.candidateLeaf_parent",
    "BB6.Agent19Raw10CryptidsLeaf.raw10RemainderWithCandidate_exact",
    "BB6.Agent19Raw10CryptidsLeaf.raw10RemainderWithCandidate_disjoint",
    "BB6.Agent19Raw10CryptidsLeaf.raw10RemainderWithCandidate_count",
    "BB6.Agent19Raw10CryptidsLeaf.raw10RemainderWithCandidate_mass",
    "BB6.Agent19Raw10CryptidsLeaf.raw10CoverWithCandidate",
    "BB6.Agent19Raw10CryptidsLeaf.exact_from_raw10_remainder_with_candidate",
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
    "claim": "one pinned Cryptids NonHalt root is a genuine raw10 last-hole leaf; the exact 41-box complement becomes 49 residual boxes",
    "source_module": "BusyBeaver.BB6.NonHalt.M_1RB0LC_1LC0RE_1LA1LD_1LA1LB_0RF1RA_HHH0RE",
    "upstream_commit": "3647718b5df22e1a61462dec0376bd204526285a",
    "leaf_completions": 25,
    "pre_leaf": {"boxes": 41, "mass": 90737503713725},
    "post_leaf": {"boxes": 49, "mass": 90737503713700},
    "mass_removed": 25,
    "module_count": manifest["module_count"],
    "reused_precompiled_modules": manifest.get("precompiled_core", {}).get("reused_module_count", 0),
    "theorem_axioms": {name: sorted(profiles[name]) for name in required},
}
pathlib.Path(sys.argv[3]).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
print(json.dumps(summary, indent=2, sort_keys=True))
PY

#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
UPSTREAM_ROOT="${UPSTREAM_ROOT:?set UPSTREAM_ROOT to the pinned Cryptids checkout}"
WORKDIR="${WORKDIR:-/tmp/agent50-raw10-ctl-footprint}"
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
test -s "$ROOT/.tmp/a47-canonical/imports/BB6Coverage.lean"

python3 "$ROOT/tools/test_lean_compile_module_index.py"
mkdir -p "$WORKDIR"
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
  "$ROOT/im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprint.lean" \
  "$ROOT/im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprintSecond.lean" \
  "$ROOT/im-results/agent50-weighted-tnf-pilot/Raw10CtlDualConsumer.lean" \
  --workdir "$WORKDIR/build" --source-root "$UPSTREAM_ROOT" --jobs "$JOBS" \
  --lean "$WORKDIR/lean-with-upstream" --manifest "$WORKDIR/build/manifest.json" \
  --label raw10-ctl-footprint-minimal-source-closure \
  --provenance-input "$WORKDIR/upstream-commit.txt" \
  --provenance-input "$WORKDIR/upstream-dependencies.sha256" \
  --provenance-input "$ROOT/im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprint.lean" \
  --provenance-input "$ROOT/im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprintSecond.lean" \
  --provenance-input "$ROOT/im-results/agent50-weighted-tnf-pilot/Raw10CtlDualConsumer.lean" \
  --override Raw10CtlFootprint=im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprint.lean \
  --override Raw10CtlFootprintSecond=im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprintSecond.lean \
  --override Raw10CtlDualConsumer=im-results/agent50-weighted-tnf-pilot/Raw10CtlDualConsumer.lean \
  --override Raw10BoxCore=im-results/agent49-box-complement/Raw10BoxCore.lean \
  --override Raw10FixedLeaves=im-results/agent13-block-far/Raw10FixedLeaves.lean \
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
  --override BB6Coverage=.tmp/a47-canonical/imports/BB6Coverage.lean \
  --override BlankDelayKernel=im-results/agent13-weighted-first-one/BlankDelayKernel.lean \
  --override BlankDelaySource=im-results/agent13-weighted-first-one/BlankDelaySource.lean \
  --override SparseBlankDelay=im-results/agent13-weighted-first-one/SparseBlankDelay.lean \
  --override WeightedTNF=im-results/agent13-weighted-first-one/WeightedTNF.lean \
  --override WeightedTNFCertificate=im-results/agent13-weighted-first-one/WeightedTNFCertificate.lean \
  --override WeightedFirstOneCover=im-results/agent13-weighted-first-one/WeightedFirstOneCover.lean \
  --override ZipPrefixAudit=im-results/agent48-prefix-audit/ZipPrefixAudit.lean \
  --override ZipThreeHoleAudit=im-results/agent10-tnf-multipump/ZipThreeHoleAudit.lean \
  --override ZipAuditCore=im-results/agent10-tnf-multipump/ZipAuditCore.lean \
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
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
}
required = [
    "BB6.Agent50CtlFootprint.source2_eq_pinned",
    "BB6.Agent50CtlFootprint.toAgent8_ofAgent8",
    "BB6.Agent50CtlFootprint.ofAgent8_candidate2_toBB",
    "BB6.Agent50CtlFootprint.ctlCheck_congr",
    "BB6.Agent50CtlFootprint.ctl_certificate_implies_is_does_not_halt_of_agreement",
    "BB6.Agent50CtlFootprint.ctlAcc2_footprint",
    "BB6.Agent50CtlFootprint.ctlCheck_target2",
    "BB6.Agent50CtlFootprint.ctlLeaf2_neverHalts",
    "BB6.Agent50CtlFootprint.ctlLeaf2_assignedCount",
    "BB6.Agent50CtlFootprint.ctlLeaf2_holes_exact",
    "BB6.Agent50CtlFootprint.ctlLeaf2_completionCount",
    "BB6.Agent50CtlFootprintSecond.source3_eq_pinned",
    "BB6.Agent50CtlFootprintSecond.toAgent8_ofAgent8_3",
    "BB6.Agent50CtlFootprintSecond.ofAgent8_candidate3_toBB",
    "BB6.Agent50CtlFootprintSecond.ctlAcc3_footprint",
    "BB6.Agent50CtlFootprintSecond.ctlCheck_target3",
    "BB6.Agent50CtlFootprintSecond.ctlLeaf3_neverHalts",
    "BB6.Agent50CtlFootprintSecond.ctlLeaf3_assignedCount",
    "BB6.Agent50CtlFootprintSecond.ctlLeaf3_holes_exact",
    "BB6.Agent50CtlFootprintSecond.ctlLeaf3_completionCount",
    "BB6.Agent50Raw10CtlDualConsumer.cycleCover",
    "BB6.Agent50Raw10CtlDualConsumer.haltCover",
    "BB6.Agent50Raw10CtlDualConsumer.ctlLeaf2Certificate",
    "BB6.Agent50Raw10CtlDualConsumer.ctlLeaf3Certificate",
    "BB6.Agent50Raw10CtlDualConsumer.raw10RemainderWithBothCtl_exact",
    "BB6.Agent50Raw10CtlDualConsumer.raw10RemainderWithBothCtl_disjoint",
    "BB6.Agent50Raw10CtlDualConsumer.raw10RemainderWithBothCtl_count",
    "BB6.Agent50Raw10CtlDualConsumer.ctlLeaves_disjoint",
    "BB6.Agent50Raw10CtlDualConsumer.ctlLeaves_assignedCount",
    "BB6.Agent50Raw10CtlDualConsumer.raw10RemainderWithBothCtl_mass",
    "BB6.Agent50Raw10CtlDualConsumer.raw10CoverWithBothCtl",
]
missing = [name for name in required if name not in profiles]
if missing:
    raise SystemExit("missing required axiom profiles: " + ", ".join(missing))
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = {name: sorted(profiles[name] - allowed) for name in required if profiles[name] - allowed}
if bad:
    raise SystemExit("unexpected theorem axioms: " + json.dumps(bad, sort_keys=True))
if "sorryAx" in log or "native_decide" in log:
    raise SystemExit("forbidden sorryAx/native_decide marker in compilation log")
summary = {
    "claim": "two pinned CTL certificates are replayed and consumed in an exact 51-box Raw10 parent complement; both CTL cylinders are nonhalting",
    "upstream_repository": "google-deepmind/cryptids",
    "upstream_commit": "3647718b5df22e1a61462dec0376bd204526285a",
    "source_modules": [
        "BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH",
        "BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA"
    ],
    "source_ctl_footprint": ["A0=1RB", "B0=1LC", "C1=1LE", "E0=0LE"],
    "certificates": [
        {"fixed_transitions": 4, "free_transitions": 8, "completion_count": 152587890625,
         "footprint": ["A0=1RB", "B0=1LC", "C1=1LE", "E0=0LE"]},
        {"fixed_transitions": 5, "free_transitions": 7, "completion_count": 6103515625,
         "footprint": ["A0=1RB", "A1=0RC", "B0=1LC", "C0=1RA", "C1=1RC"]}
    ],
    "raw10_parent_consumer": {
        "remaining_boxes": 51,
        "remaining_mass": 90578812307475,
        "removed_mass": 158691406250,
        "ctl_cylinders_disjoint": True,
        "union_assigned_slots": 6
    },
    "module_count": manifest["module_count"],
    "theorem_axioms": {name: sorted(profiles[name]) for name in required},
}
pathlib.Path(sys.argv[3]).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
print(json.dumps(summary, indent=2, sort_keys=True))
PY

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
  --workdir "$WORKDIR/build" --source-root "$UPSTREAM_ROOT" --jobs "$JOBS" \
  --lean "$WORKDIR/lean-with-upstream" --manifest "$WORKDIR/build/manifest.json" \
  --label raw10-ctl-footprint-minimal-source-closure \
  --provenance-input "$WORKDIR/upstream-commit.txt" \
  --provenance-input "$WORKDIR/upstream-dependencies.sha256" \
  --provenance-input "$ROOT/im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprint.lean" \
  --provenance-input "$ROOT/im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprintSecond.lean" \
  --override Raw10CtlFootprint=im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprint.lean \
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
    "claim": "two pinned CTL certificates are replayed over their exact four- and five-transition footprints; all completions of both cylinders are nonhalting",
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
    "module_count": manifest["module_count"],
    "theorem_axioms": {name: sorted(profiles[name]) for name in required},
}
pathlib.Path(sys.argv[3]).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
print(json.dumps(summary, indent=2, sort_keys=True))
PY

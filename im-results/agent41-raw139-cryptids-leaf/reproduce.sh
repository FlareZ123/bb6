#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
UPSTREAM_ROOT="${UPSTREAM_ROOT:?set UPSTREAM_ROOT to the pinned Cryptids checkout}"
CANONICAL77_DIR="${CANONICAL77_DIR:?set CANONICAL77_DIR to the accepted canonical77 artifact}"
CHAMPION_BUILD_DIR="${CHAMPION_BUILD_DIR:?set CHAMPION_BUILD_DIR to the champion-residual build directory}"
WORKDIR="${WORKDIR:-/tmp/agent41-raw139-cryptids-leaf}"
LEAN_BIN="${LEAN_BIN:-$HOME/.elan/bin/lean}"
PINNED="3647718b5df22e1a61462dec0376bd204526285a"
MODULE="BusyBeaver.BB6.NonHalt.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH"

test "$(git -C "$UPSTREAM_ROOT" rev-parse HEAD)" = "$PINNED"
test -s "$CANONICAL77_DIR/CanonicalTwoParentGraft.olean"
test -s "$CHAMPION_BUILD_DIR/ChampionF1OneLBIntegration.olean"
test -s "$UPSTREAM_ROOT/.lake/build/lib/BusyBeaver/Bridge.olean"
test -s "$UPSTREAM_ROOT/.lake/build/lib/BusyBeaver/BB6/NonHalt/M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH.olean"

mkdir -p "$WORKDIR"
export LEAN_PATH="$CANONICAL77_DIR:$CHAMPION_BUILD_DIR:$UPSTREAM_ROOT/.lake/build/lib${LEAN_PATH:+:$LEAN_PATH}"
"$LEAN_BIN" --version | tee "$WORKDIR/lean-version.txt"

compile() {
  local module="$1"
  local source="$2"
  "$LEAN_BIN" -o "$CHAMPION_BUILD_DIR/$module.olean" "$ROOT/$source" 2>&1 | tee -a "$WORKDIR/compile.log"
  if grep -Eq 'sorryAx|native_decide' "$WORKDIR/compile.log"; then
    echo "Forbidden sorryAx/native_decide marker while compiling $module" >&2
    exit 1
  fi
}

: > "$WORKDIR/compile.log"
compile RelativeTape im-results/agent4-coverage-smoke/RelativeTape.lean
compile CryptidsTapeAdapter im-results/agent4-coverage-smoke/CryptidsTapeAdapter.lean
compile WeightedNonhaltLeafAdapter im-results/agent47-weighted-halt-branch/WeightedNonhaltLeafAdapter.lean
compile HardRootCore im-results/agent19-hard-root-crosswalk/HardRootCore.lean
compile HardRootParents im-results/agent19-hard-root-crosswalk/HardRootParents.lean
compile HardRootLeaves im-results/agent19-hard-root-crosswalk/HardRootLeaves.lean
compile Raw139CryptidsLeafPilot im-results/agent41-raw139-cryptids-leaf/Raw139CryptidsLeafPilot.lean

python3 - "$WORKDIR/compile.log" "$WORKDIR/summary.json" <<'PY'
import json, pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
required = (
    "BB6.Agent41Raw139CryptidsLeaf.original_eq_candidate",
    "BB6.Agent41Raw139CryptidsLeaf.original_never",
    "BB6.Agent41Raw139CryptidsLeaf.candidate_never",
    "BB6.Agent41Raw139CryptidsLeaf.candidate_first_hole_path",
    "BB6.Agent41Raw139CryptidsLeaf.candidateTail_endpoint",
    "BB6.Agent41Raw139CryptidsLeaf.candidateTail_pathOK",
    "BB6.Agent41Raw139CryptidsLeaf.candidateWeightedLeaf",
    "BB6.Agent41Raw139CryptidsLeaf.candidateFrontier_sound",
    "BB6.Agent41Raw139CryptidsLeaf.candidateRemaining_sound",
    "BB6.Agent41Raw139CryptidsLeaf.candidateParent_current_entry",
    "BB6.Agent41Raw139CryptidsLeaf.candidateParent_current_unique",
    "BB6.Agent41Raw139CryptidsLeaf.exact_from_canonical77_and_raw139_candidate_leaf",
)
profiles = {
    name: {x.strip() for x in raw.split(",") if x.strip()}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \\[([^\\]]*)\\]", log)
}
missing = [name for name in required if name not in profiles]
if missing:
    raise SystemExit("missing axiom profiles: " + ", ".join(missing))
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = {name: sorted(profiles[name] - allowed) for name in required if profiles[name] - allowed}
if bad:
    raise SystemExit("unexpected theorem axioms: " + json.dumps(bad, sort_keys=True))
summary = {
    "status": "Lean 4.36.0-rc2 source-connected raw139 leaf/frontier compile",
    "candidate_rle": "1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---",
    "source_module": "BusyBeaver.BB6.NonHalt.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH",
    "upstream_commit": "3647718b5df22e1a61462dec0376bd204526285a",
    "source_leaf_completions": 25,
    "first_hole": "F1",
    "first_hole_time": 27,
    "current_parent_address": ["D1=0LE", "E1=1LF"],
    "current_frontier_count_before_refinement": 102,
    "theorem_axioms": {name: sorted(profiles[name]) for name in required},
}
pathlib.Path(sys.argv[2]).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
print(json.dumps(summary, indent=2, sort_keys=True))
PY

sha256sum "$WORKDIR/compile.log" > "$WORKDIR/compile.log.sha256"
printf '%s\n' "$PINNED" > "$WORKDIR/upstream-commit.txt"

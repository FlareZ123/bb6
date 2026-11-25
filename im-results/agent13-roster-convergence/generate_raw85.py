"""Generate raw85/F1=1RA using destination-table FAR validation.

DFA lookup keys are only a candidate-ordering heuristic. Every candidate is
re-saturated against the actual destination table and exact orientation; the
generated Lean Audit is the semantic acceptance boundary.
"""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
GENERATOR_DIR = HERE.parent / "agent31-three-hole-tnf"
sys.path.insert(0, str(GENERATOR_DIR))
import generate_four_hole_sibling as sibling

OUTPUT_DIR = HERE / "raw85"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
sibling.ROOT = OUTPUT_DIR
sibling.PARENT = "1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA"

# Keep raw85's new sweeps separate from the shared core's SweepData.
import generate_sweeps as sweeps

RAW85_SWEEPS = [
    "1RB0LE_1RC1LF_0RD1RF_1LD1RE_---0LB_0RC1RA",
    "1RB0LE_1RC1LF_0RD---_1LD1RE_1RA0LB_0RF1RA",
    "1RB0RD_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC1RA",
]
sibling.PUMPS = {sweeps.parse(p): i for i, p in enumerate(RAW85_SWEEPS, 10)}
parts = ["import SweepPumping", "set_option maxRecDepth 100000",
         "set_option maxHeartbeats 0", "set_option linter.unusedVariables false",
         "namespace BB6Coverage.Agent21Raw85Pump", "open BB6Coverage"]
for i, table in enumerate(RAW85_SWEEPS, 10):
    p = sweeps.parse(table)
    ans = sweeps.candidate(p, sweeps.concrete_events(p))
    if ans is None:
        raise RuntimeError(f"raw85 sweep missing: {table}")
    code, info = sweeps.generate(i, p, ans)
    print("RAW85_SWEEP", i, table, info)
    parts.append(code)
parts.append("end BB6Coverage.Agent21Raw85Pump")
(OUTPUT_DIR / "Raw85SweepData.lean").write_text("\n\n".join(parts) + "\n", encoding="utf-8")


def read_candidate_bank(path: Path):
    candidates = []
    if not path.exists():
        return candidates
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 6:
            raise ValueError(f"{path}:{line_number}: expected four key tokens, orientation, DFA")
        _historical_key = tuple(fields[:4])  # ordering metadata only, never a proof premise
        rev = int(fields[4])
        dfa = [int(x, 36) for x in fields[5]]
        if rev not in (0, 1):
            raise ValueError(f"{path}:{line_number}: orientation must be 0 or 1")
        if len(dfa) < 2 or len(dfa) % 2 or dfa[0] != 0:
            raise ValueError(f"{path}:{line_number}: candidate must be even-sized and satisfy delta(0, false)=0")
        candidates.append((rev, dfa))
    return candidates


candidate_dir = HERE.parent / "agent21-raw85"
canonical_path = candidate_dir / "dfa-candidates.txt"
smt_path = candidate_dir / "smt-candidates.txt"
canonical = read_candidate_bank(canonical_path)
if len(canonical) != 14:
    raise RuntimeError(f"expected 14 canonical raw85 candidates, found {len(canonical)}")
if not smt_path.exists():
    raise FileNotFoundError("commit the eight workflow-validated records as im-results/agent21-raw85/smt-candidates.txt")
smt = read_candidate_bank(smt_path)
if not smt or len(smt) > 8:
    raise RuntimeError(f"expected one to eight exact-target SMT candidates, found {len(smt)}")
extra = []
for bank_name, bank in ((canonical_path.name, canonical), (smt_path.name, smt)):
    print(f"RAW85_CANDIDATE_BANK {bank_name} {len(bank)}")
    extra.extend(candidate for candidate in bank if candidate not in extra)

sibling.EXTRA_DFAS = extra
print(f"RAW85_EXTRA_DFAS {len(sibling.EXTRA_DFAS)}")
for pattern in ("FourHoleSibling*.lean", "Raw85Sibling*.lean"):
    for stale in OUTPUT_DIR.glob(pattern):
        stale.unlink()

# Preflight the entire recursive split tree so one missing leaf does not hide
# the rest of the uncovered frontier. This is a search diagnostic only;
# successful leaves are still checked by the generated Lean Audit.
from collections import Counter
scan_stats = Counter()
uncovered = []

def scan_candidates(p, depth=1):
    result = sibling.classify(p)
    typ = result[0]
    if typ == "cycle":
        scan_stats["cycle"] += 1
        return
    if typ == "open":
        if p in sibling.PUMPS:
            scan_stats["proven"] += 1
            return
        key = tuple(p[i] for i in (5, 1, 8, 10))
        candidates = []
        if key in sibling.DFAS:
            candidates.append(sibling.DFAS[key])
        candidates.extend(v for v in sibling.EXTRA_DFAS if v not in candidates)
        candidates.extend(v for v in sibling.DFAS.values() if v not in candidates)
        chosen = None
        for rev, dfa in candidates:
            try:
                sibling.masks(p, rev, dfa)
                chosen = (rev, dfa)
                break
            except AssertionError:
                continue
        if chosen is None:
            uncovered.append((depth, sibling.show(p), key))
            scan_stats["uncovered"] += 1
        else:
            scan_stats["far"] += 1
        return
    _, n, slot = result
    if p.count("---") == 1:
        scan_stats["last"] += 1
        return
    scan_stats["split"] += 1
    for move in sibling.MOVES:
        scan_candidates(sibling.refine(p, slot, move), depth + 1)

scan_candidates(sibling.parse(sibling.PARENT))
print("RAW85_CANDIDATE_SCAN", dict(scan_stats))
for depth, table, key in uncovered:
    print("RAW85_UNCOVERED", depth, table, key)
if uncovered:
    report = ["# Raw85 candidate coverage scan", "", f"Counts: {dict(scan_stats)}", "", "| Depth | Open table | Lookup key |", "|---:|---|---|"]
    report.extend(f"| {depth} | {table} | {' '.join(key)} |" for depth, table, key in uncovered)
    (OUTPUT_DIR / "Raw85CandidateCoverage.md").write_text("\n".join(report) + "\n")
    raise SystemExit(f"{len(uncovered)} raw85 open leaves remain uncovered by the candidate bank")

sibling.main()

# Preserve an explicit equality between the generated path-end parent and the
# literal source table. This checks the path witness, not the candidate keys.
parsed = sibling.parse(sibling.PARENT)
expr = "none"
for i in reversed(range(12)):
    value = "none" if parsed[i] == "---" else f"some (some {sibling.move(parsed[i])})"
    slot = f"({i // 2}, {str(bool(i % 2)).lower()})"
    expr = f"(if s = {slot} then {value} else {expr})"

base_path = OUTPUT_DIR / "FourHoleSiblingBase.lean"
source = base_path.read_text()
newline = chr(10)
assert source.startswith("import ThreeHoleAudit" + newline)

footer = "end BB6.Agent31FourHoleSibling"
diagnostic = f"""
def sourceParent : PartialMachine := fun s => {expr}

theorem wideParent_matches_sourceParent : wideParent = sourceParent := by
  funext s
  rcases s with ⟨q, b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

#print axioms wideParent_matches_sourceParent
"""
idx = source.rfind(footer)
if idx < 0:
    raise RuntimeError("Could not locate sibling namespace footer")
base_path.write_text(source[:idx] + newline + diagnostic + newline + source[idx:])

# Give this sibling tree a unique module and namespace identity.
for path in sorted(OUTPUT_DIR.glob("FourHoleSibling*.lean")):
    source = path.read_text(encoding="utf-8")
    source = source.replace("BB6.Agent31FourHoleSibling", "BB6.Agent21Raw85Sibling")
    source = source.replace("FourHoleSibling", "Raw85Sibling")
    source = source.replace("import SweepData\n", "import Raw85SweepData\n")
    source = source.replace("BB6Coverage.Agent31Pump.", "BB6Coverage.Agent21Raw85Pump.")
    target = path.with_name(path.name.replace("FourHoleSibling", "Raw85Sibling"))
    target.write_text(source, encoding="utf-8")
    path.unlink()

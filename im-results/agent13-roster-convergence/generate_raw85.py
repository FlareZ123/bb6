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
candidate_files = [
    candidate_dir / "dfa-candidates.txt",
    candidate_dir / "smt-candidates.txt",
]
extra = []
for candidate_file in candidate_files:
    bank = read_candidate_bank(candidate_file)
    print(f"RAW85_CANDIDATE_BANK {candidate_file.name} {len(bank)}")
    extra.extend(candidate for candidate in bank if candidate not in extra)

sibling.EXTRA_DFAS = extra
print(f"RAW85_EXTRA_DFAS {len(sibling.EXTRA_DFAS)}")
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
source = "import Mathlib" + newline + source
expected_import_prefix = "import Mathlib" + newline + "import ThreeHoleAudit" + newline
if not source.startswith(expected_import_prefix):
    raise RuntimeError("Import newline regression: generated imports are not separate lines")
if "import Mathlib" + chr(92) + "nimport" in source:
    raise RuntimeError("Literal backslash-n found in generated import block")

footer = "end BB6.Agent31FourHoleSibling"
diagnostic = f"""
def sourceParent : PartialMachine := fun s => {expr}

theorem wideParent_matches_sourceParent : wideParent = sourceParent := by
  funext s
  rcases s with ⟨q, b⟩
  fin_cases q <;> cases b <;> decide

#print axioms wideParent_matches_sourceParent
"""
idx = source.rfind(footer)
if idx < 0:
    raise RuntimeError("Could not locate sibling namespace footer")
base_path.write_text(source[:idx] + newline + diagnostic + newline + source[idx:])

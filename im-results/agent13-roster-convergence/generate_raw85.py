"""Strict raw85/F1=1RA parent and exact-DFA-key diagnostic.

This wrapper reuses Agent31's sibling generator but forbids cross-key DFA
fallbacks. It is a diagnostic/acceptance gate, not a claim that raw85 is
closed. A missing exact key is reported and leaves the sibling tree open.
"""
from collections import Counter
from pathlib import Path
import sys

GENERATOR_DIR = Path(__file__).resolve().parents[1] / "agent31-three-hole-tnf"
sys.path.insert(0, str(GENERATOR_DIR))
import generate_four_hole_sibling as sibling

OUTPUT_DIR = Path(__file__).resolve().parent / "raw85"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
sibling.ROOT = OUTPUT_DIR
sibling.PARENT = "1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA"

original_build = sibling.build
original_dfas = sibling.DFAS
missing_dfa_keys = Counter()
all_open_keys = Counter()

class MissingExactDFAKey(Exception):
    pass

def strict_build(p, depth=1):
    result = sibling.classify(p)
    if result[0] == "open" and p not in sibling.PUMPS:
        key = tuple(p[i] for i in (5, 1, 8, 10))
        all_open_keys[key] += 1
        if key not in original_dfas:
            missing_dfa_keys[key] += 1
            raise MissingExactDFAKey(key)
        previous = sibling.DFAS
        sibling.DFAS = {key: original_dfas[key]}
        try:
            return original_build(p, depth)
        finally:
            sibling.DFAS = previous
    return original_build(p, depth)

sibling.build = strict_build
try:
    sibling.main()
except MissingExactDFAKey as error:
    print("RAW85_MISSING_EXACT_DFA_KEY", error.args[0])
print("RAW85_OPEN_DFA_KEYS_SEEN", sorted(all_open_keys.items()))
print("RAW85_MISSING_EXACT_DFA_KEYS", sorted(missing_dfa_keys.items()))

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

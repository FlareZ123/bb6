"""Generate and cross-check the raw85 / F1=1RA four-hole sibling.

The underlying generator is Agent31's source-checked four-hole sibling
pipeline. This wrapper changes only the root partial table and output
directory, keeping generated modules isolated from Agent11's F1=0RA run.
It also emits a Lean equality check between the path-built parent and the
literal table parsed by the Python audit builder.
"""
from pathlib import Path
import sys

GENERATOR_DIR = Path(__file__).resolve().parents[1] / "agent31-three-hole-tnf"
sys.path.insert(0, str(GENERATOR_DIR))
import generate_four_hole_sibling as sibling

OUTPUT_DIR = Path(__file__).resolve().parent / "raw85"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

sibling.ROOT = OUTPUT_DIR
sibling.PARENT = "1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA"
sibling.main()

parsed = sibling.parse(sibling.PARENT)
expr = "none"
for i in reversed(range(12)):
    value = "none" if parsed[i] == "---" else f"some (some {sibling.move(parsed[i])})"
    slot = f"({i // 2}, {str(bool(i % 2)).lower()})"
    expr = f"(if s = {slot} then {value} else {expr})"

base_path = OUTPUT_DIR / "FourHoleSiblingBase.lean"
source = base_path.read_text()
marker = "\\nend BB6.Agent31FourHoleSibling\\n"
diagnostic = f"""
def sourceParent : PartialMachine := fun s => {expr}

theorem wideParent_matches_sourceParent : wideParent = sourceParent := by
  funext s
  rcases s with ⟨q, b⟩
  fin_cases q <;> cases b <;> decide

#print axioms wideParent_matches_sourceParent
"""
if marker not in source:
    raise RuntimeError("Could not locate sibling namespace footer")
base_path.write_text(source.replace(marker, "\\n" + diagnostic + marker))

"""Generate a width-eight block-FAR certificate for frozen q0-149 index 10."""
from pathlib import Path
import sys, re, subprocess
root = Path(__file__).resolve().parents[2]
block = root / "im-results/agent13-block-far"
out = Path(__file__).resolve().parent
sys.path.insert(0, str(block))
from generate_multi import generate
from emit_active import emit_active, specialize_active
subprocess.run([sys.executable, str(block / "specialize.py"), "8"], check=True)
src = (block / "SparseBlockFAR.lean").read_text()
src = src.replace("import BlockFAR", "import BlockFAR8").replace("BB6BlockFAR", "BB6BlockFAR8")
src = re.sub(r"\b48\b", "1536", src)
src = re.sub(r"\b8\b", "256", src)
(block / "SparseBlockFAR8.lean").write_text(src)
specialize_active(block, 8)
table = "1RB1LC_1RC0RC_0LA0RD_1RB1RE_0RF---_1LC0LC"
data = generate(table, out, width=8, cap=2, mod=1, runs=4, flip=False,
                name="Q0149Index10", minimize_left=True, sparse=True,
                offset=0, left_mode="suffix")
emit_active(data, out, "Q0149Index10")
print("Certified candidate sizes", data["left_states"], data["right_nodes"])
(out / "Raw11Q0Ten149.lean").write_text("""import Q0149Index10Proof
import BlockFARBridge8
import Agent5Frame150
set_option maxHeartbeats 0
namespace BB6BlockFAR8.Q0149Index10
open BB6Coverage BB6.Agent13BlankDelay
def table : PartialMachine := partialTable machine
theorem never_source (m : Machine) (hm : compatible table m) : NeverHalts m :=
  transfer_never machine m hm never
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never_source m hm)
#print axioms cover
end BB6BlockFAR8.Q0149Index10
""")

"""Generate the block-FAR witness for the last 0RA leaf."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent13-block-far"))
from generate_multi import generate

TABLE = "1RB0LF_1RC---_0RD0RC_1LD1RE_0RA1LE_0LA1LC"
NAME = "Raw120RA423Block"

if __name__ == "__main__":
    generate(TABLE, ROOT, width=3, cap=1, mod=3, runs=2, flip=False,
             name=NAME, minimize_left=True, sparse=True)
    (ROOT / (NAME + "Adapter.lean")).write_text("""import Raw120RA423BlockProof
import BlockFARBridge

namespace BB6Coverage.Agent3RA423Block
open BB6Coverage

def table : PartialMachine := BB6BlockFAR.partialTable BB6BlockFAR.Raw120RA423Block.machine
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6BlockFAR.transfer_never BB6BlockFAR.Raw120RA423Block.machine m hm
    BB6BlockFAR.Raw120RA423Block.never
#print axioms never
end BB6Coverage.Agent3RA423Block
""")

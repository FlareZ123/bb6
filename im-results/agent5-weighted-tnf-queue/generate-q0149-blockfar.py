"""Generate the last two q0-149 leaf certificates (exact block-FAR saturation).
python generate-q0149-blockfar.py OUTDIR ID
IDs are zero-based exact-frontier leaf indices. No search.
"""
from pathlib import Path
import subprocess,sys
block=Path(__file__).resolve().parents[1]/'agent13-block-far'
sys.path.insert(0,str(block))
from generate_multi import generate
from emit_active import emit_active,specialize_active
CASES={
    8:("1RB1LC_1RC0LC_0LA0RD_1RF1RE_0RB---_1LB1RE",9,3),
    10:("1RB1LC_1RC0RC_0LA0RD_1RB1RE_0RF---_1LC0LC",6,5)
}
out=Path(sys.argv[1]);i=int(sys.argv[2]);t,w,k=CASES[i];name=f'Q0149Block{i}';ns=f'BB6BlockFAR{w}.{name}'
subprocess.run([sys.executable,str(block/'specialize.py'),str(w)],check=True)
specialize_active(block,w)
# The older dense proof emitter is discarded; the source certificate uses the
# support-complete sparse checker, which validates every omitted symbol.
out.mkdir(parents=True,exist_ok=True)
data=generate(t,out,w,1,1,k,False,name,minimize_left=True,sparse=True,left_mode='suffix',data_only=True)
emit_active(data,out,name)
(out/f'{name}.lean').write_text(f"""import {name}Proof
import BlockFARBridge{w}
import WeightedTNF
namespace BB6.Agent50Q0149Block{i}
open BB6Coverage BB6.Agent13BlankDelay
def table : PartialMachine := BB6BlockFAR{w}.partialTable {ns}.machine
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6BlockFAR{w}.transfer_never {ns}.machine m hm {ns}.never
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms cover
end BB6.Agent50Q0149Block{i}
""")

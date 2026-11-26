"""Emit the checked sparse width-12 certificate for E0=0LF residual 1307.

Usage: python emit1307.py OUTPUT_DIR
Proof dependencies: Agent13's BlockMacro12, BlockFAR12, SparseBlockFAR12,
ActiveSparseFAR12, RangeCheck12 and BlockFARBridge12. Generate the width-specific
files using Agent13's specialization scripts before source audit.
"""
from pathlib import Path
from itertools import repeat
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"agent48-raw139-f1-oneRA"))
sys.path.insert(0,str(HERE.parent/"agent13-block-far"))
from blockcert import generate
from sparse_min import minimize,check
from emit_active import emit_active

TABLE=[7,13,11,17,14,21,24,16,20,11,1,2]
WIDTH=12
def left_key(xs,a):
    if not xs and a==0:return ()
    tail,parity=xs or ((),0)
    return (tail+(a,))[-3:],(parity+a.bit_count())%2

def dense_iter(entries,size,default):
    """Stream the emitter's dense input interface without allocating its arrays."""
    i=0
    for j,v in sorted(entries.items()):
        assert i<=j<size
        yield from repeat(default,j-i)
        yield v
        i=j+1
    yield from repeat(default,size-i)

def main(out):
    raw=generate(TABLE,width=WIDTH,flip=False,left_key=left_key,raw_graph=True,event_limit=50000)
    assert raw is not None
    cert=minimize(TABLE,WIDTH,False,raw)
    print("Checked",cert['left_states'],cert['right_nodes'],check(TABLE,cert,False),flush=True)
    A=1<<WIDTH;D=cert['left_states'];C=cert['right_nodes'];dead=C-1
    data={**cert,
        'push':dense_iter({l*A+a:j for (l,a),j in cert['push'].items()},D*A,0),
        'ctrl':dense_iter({12*l+2*q+d:v for (l,q,d),v in cert['ctrl'].items()},12*D,dead),
        'aux':dense_iter({A*(6*l+q)+b:v for (l,q,b),v in cert['aux'].items()},6*A*D,dead),
        'edges':dense_iter({A*v+a:ts for (v,a),ts in cert['edges'].items()},C*A,[])}
    out.mkdir(parents=True,exist_ok=True)
    name="E0LFResidual1307"
    emit_active(data,out,name)
    (out/(name+".lean")).write_text("""import E0LFResidual1307Proof
import BlockFARBridge12
import FastThreeHoleAudit

namespace BB6.Agent3E0LFResidual1307
def ctr : BB6Coverage.PartialMachine := BB6Coverage.FAR.fromCodes [7,13,11,17,14,21,24,16,20,11,1,2]

theorem same : ctr = BB6BlockFAR12.partialTable BB6BlockFAR12.E0LFResidual1307.machine := by
  funext s
  rcases s with ⟨q,b⟩
  have h : ∀ (q : Fin 6) (b : Bool), ctr (q,b) = BB6BlockFAR12.partialTable BB6BlockFAR12.E0LFResidual1307.machine (q,b) := by decide +kernel
  exact h q b

theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) : BB6Coverage.NeverHalts m :=
  BB6BlockFAR12.transfer_never BB6BlockFAR12.E0LFResidual1307.machine m (by rw [← same]; exact hm) BB6BlockFAR12.E0LFResidual1307.never

#print axioms never
end BB6.Agent3E0LFResidual1307
""")
if __name__=="__main__":
    main(Path(sys.argv[1]))

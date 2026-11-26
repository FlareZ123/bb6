"""Generate a kernel-checkable reflected width-two certificate for residual 4125.

Run from any directory: python im-results/agent3-raw139-zeroLF-context/emit4125.py OUT
The generator is untrusted; BlockFAR2 checks all proof obligations in Lean.
"""
from pathlib import Path
import sys

base=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(base/'agent48-raw139-f1-oneLA'))
sys.path.insert(0,str(base/'agent48-raw139-f1-oneRA'))
from blockcert import generate
from package import block_source

TABLE=[7,9,11,24,14,21,2,16,20,11,3,0]

def raw_run_key(width,p,k,cap,mod,onesmod):
    """Read each block's raw bits in far-to-near order.
    Retain the first p runs, last k runs, capped run lengths and residues,
    total length residue, and total number of ones residue.
    """
    def push(xs,a):
        for i in range(width):
            w=(a>>i)&1
            if not xs and w==0:
                continue
            pref,tail,m,om,active=xs or ((),(),0,0,True)
            def extend(r):
                if r and r[-1][0]==w:
                    _,n,t=r[-1]
                    return r[:-1]+((w,min(n+1,cap),(t+1)%mod),)
                return r+((w,1,1%mod),)
            if active:
                np=extend(pref)
                if len(np)>p:
                    active=False
                else:
                    pref=np
            tail=extend(tail)[-k:]
            xs=(pref,tail,(m+1)%mod,(om+w)%onesmod,active)
        return xs
    return push

def emit(out):
    cert=generate(TABLE,width=2,flip=True,event_limit=100000,
                  left_key=raw_run_key(2,1,4,2,3,2))
    assert cert is not None, "candidate synthesis failed"
    print("minimized",cert['left_states'],cert['right_nodes'],flush=True)
    # The source bridge uses the exact original unreflected table.
    ns="BB6.Agent3E0LFResidual4125"
    src=block_source(4125,TABLE,cert)
    src=src.replace("BB6.Agent48F1OneRABlocks.H4125",ns)
    src=src[:src.index("theorem same :")]
    src+="""
theorem same : BB6Coverage.FAR.reflectPartial ctr = BB6BlockFAR.partialTable machine := by
  funext s
  rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool,
      BB6Coverage.FAR.reflectPartial ctr (q,b) =
      BB6BlockFAR.partialTable machine (q,b) := by decide +kernel
  exact h q b

theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) :
    BB6Coverage.NeverHalts m := by
  apply BB6Coverage.FAR.reflectNever m
  apply BB6BlockFAR.transfer_never machine (BB6Coverage.reflectTable m)
  · rw [← same]
    exact BB6Coverage.FAR.reflectCompatible ctr m hm
  · exact forever
#print axioms valid
#print axioms never
end """+ns+"\n"
    out.mkdir(parents=True,exist_ok=True)
    header=("import BlockFAR2\nimport BlockFARBridge\nimport FastThreeHoleAudit\n"
            "import FARBi\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n")
    (out/'E0LFResidual4125.lean').write_text(header+src)

if __name__=='__main__':
    emit(Path(sys.argv[1]))

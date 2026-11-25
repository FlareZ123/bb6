"""Generate an exact finite cycle of growing parametric sections.

Every local transition, sweep and section join is checked by Lean.
"""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
import multi

def emit(spec,mod,ns):
    p=multi.parse(spec["table"])
    q=spec["state"];side=spec["side"]
    prefix=spec["prefix"];block=spec["block"]
    suffixes=spec["suffixes"];entry=spec["entry"]
    N=len(suffixes)
    parts=["import SweepPumping","set_option maxRecDepth 100000",
           "set_option maxHeartbeats 0",f"namespace {ns}",
           "open BB6Coverage BB6Coverage.Agent31Pump"]
    def cfg(prefix,suffix):
        w=multi.clean(multi.lit(prefix)+multi.rep(block)+multi.lit(suffix))
        return multi.C(q,w if side=="R" else (),w if side=="L" else ())
    ab=[]
    for i,suffix in enumerate(suffixes):
        st=cfg(prefix,suffix)
        tg=cfg(prefix+block,suffixes[(i+1)%N])
        ans=multi.pump(p,st,tg,limit=spec.get("pump_limit",3000))
        assert ans is not None,(mod,i)
        code,(_,a,b)=multi.generate(i,p,(0,st,tg,ans),epoch=True)
        parts.append(code);ab.append((a,b))
        parts.append(f"def sect{i} (n : Nat) : Z0 := {multi.cfg(st)}")
    parts.append("abbrev table := M0.table")
    for i,(a,b) in enumerate(ab):
        j=(i+1)%N
        parts.append(f"""theorem advance{i} (n : Nat) : run0 table ({a}+{b}*n) (sect{i} n) = some (sect{j} (n+1)) := by
  have h : M{i}.table = table := rfl
  have H := M{i}.epoch n
  rw [h] at H
  simpa only [sect{i},sect{j},rep,{multi.SIMP}] using H""")
    A=sum(a+b*i for i,(a,b) in enumerate(ab))
    B=N*sum(b for a,b in ab)
    parts.append(f"def family (n : Nat) := sect0 ({N}*n)")
    parts.append(f"theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl")
    proof=f"theorem growth (n : Nat) : run0 table ({A}+{B}*n) (family n) = some (family (n+1)) := by\n"
    join="(advance0 ("+str(N)+"*n))"
    for i in range(1,N):
        join=f"(join0 {join} (advance{i} ({N}*n+{i})))"
    proof+=f"  have H := {join}\n"
    costs="+".join(f"({a}+{b}*({N}*n"+(f"+{i}" if i else "")+"))" for i,(a,b) in enumerate(ab))
    proof+=f"  rw [show {costs}={A}+{B}*n by omega] at H\n"
    proof+=f"  simpa only [family,show {N}*(n+1)={N}*n+{N} by omega] using H"
    parts.append(proof)
    parts.append(f"""theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {entry} (fun n => {A}+{B}*n) entry (by intro n; omega) growth m hm
#print axioms growth
#print axioms never
end {ns}""")
    (ROOT/(mod+".lean")).write_text("\n\n".join(parts)+"\n")

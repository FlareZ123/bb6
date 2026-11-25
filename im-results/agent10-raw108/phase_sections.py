"""Generate a finite chain of exact affine-parameter sections, with
one increase of the shared repetition parameter per complete cycle."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
import multi

def emit(spec,mod,ns):
    p=multi.parse(spec["table"])
    q=spec["state"];side=spec["side"];block=spec["block"]
    phases=spec["phases"];N=len(phases);entry=spec["entry"]
    parts=["import SweepPumping","set_option maxRecDepth 100000",
           "set_option maxHeartbeats 0",f"namespace {ns}",
           "open BB6Coverage BB6Coverage.Agent31Pump"]
    def cfg(prefix,suffix):
        w=multi.clean(multi.lit(prefix)+multi.rep(block)+multi.lit(suffix))
        return multi.C(q,w if side=="L" else (),w if side=="R" else ())
    ab=[]
    for i,(prefix,suffix) in enumerate(phases):
        j=(i+1)%N
        st=cfg(prefix,suffix)
        pre,suf=phases[j]
        tg=cfg(pre+(block if j==0 else ""),suf)
        ans=multi.pump(p,st,tg,limit=spec.get("pump_limit",3000))
        assert ans is not None,(mod,i)
        code,(_,a,b)=multi.generate(i,p,(0,st,tg,ans),epoch=True)
        parts.append(code);ab.append((a,b))
        parts.append(f"def sect{i} (n : Nat) : Z0 := {multi.cfg(st)}")
    parts.append("abbrev table := M0.table")
    for i,(a,b) in enumerate(ab):
        j=(i+1)%N
        parts.append(f"""theorem advance{i} (n : Nat) : run0 table ({a}+{b}*n) (sect{i} n) = some (sect{j} ({'n+1' if j==0 else 'n'})) := by
  have h : M{i}.table = table := rfl
  have H := M{i}.epoch n
  rw [h] at H
  simpa only [sect{i},sect{j},rep,{multi.SIMP}] using H""")
    A=sum(a for a,b in ab);B=sum(b for a,b in ab)
    parts.append("abbrev family := sect0")
    parts.append(f"theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl")
    join="(advance0 n)"
    for i in range(1,N):
        join=f"(join0 {join} (advance{i} n))"
    costs="+".join(f"({a}+{b}*n)" for a,b in ab)
    parts.append(f"""theorem growth (n : Nat) : run0 table ({A}+{B}*n) (family n) = some (family (n+1)) := by
  have H := {join}
  rw [show {costs}={A}+{B}*n by omega] at H
  exact H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {entry} (fun n => {A}+{B}*n) entry (by intro n; omega) growth m hm
#print axioms growth
#print axioms never
end {ns}""")
    (ROOT/(mod+".lean")).write_text("\n\n".join(parts)+"\n")

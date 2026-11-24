"""Generate the seven-phase alternating-block certificate for raw61 leaf 120."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent
shared=ROOT.parent/"agent48-raw63-counter"/"emit_counter.py"
scope={"__file__":str(shared)}
exec(shared.read_text().split("\nTABLES=",1)[0],scope)
globals().update({k:v for k,v in scope.items() if not k.startswith("__") and k!="ROOT"})
original=scope["pump"]
scope["pump"]=lambda p,s,t: original(p,s,t,3000)
p=tuple(parse("1RB0LB_1RC0LA_0RD---_1LD1RE_1RF0LB_0RC0RE"))
words=[
"00111110101010101010101010101010101010101010110011011",
"000110010101010101010101010101010101010101011001101111011",
"0011101110101010101010101010101010101010101011001101111011",
"00010110010101010101010101010101010101010101100110111101111011",
"001111110010101010101010101010101010101010101100110111101111011",
"00110101010101010101010101010101010101010101011001010101010101010110011011",
"00010101010101010101010101010101010101010101010101010101010101010101010110011011",
"001111101010101010101010101010101010101010101010101010101010101010101010110011011"]
def shape(w,k):
    m=max(re.finditer(r"(?:01)+",w),key=lambda m:m.end()-m.start())
    a=m.start()+2*k
    return cfg(3,lit(w[:a])+repeat("01","n")+lit(w[a:]),())
shapes=[shape(w,k) for w,k in zip(words,[1,1,1,1,1,1,2,15])]
out=["import Agent48CounterCore","namespace BB6.Agent48D120","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent48Counter","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",table(p)]
costs=[]
for j,(st,tg,(a,b)) in enumerate(zip(shapes,shapes[1:],[(258,12),(23,0),(258,12),(15,0),(941,20),(372,10),(15,0)])):
    co,cost=macro(p,f"stage{j}",st,tg,("n",),(a,b,0))
    out.append(co);costs.append(cost)
join="(stage0 n)"
for j in range(1,7):join=f"(join0 {join} (stage{j} n))"
out.append(f"""
def family (n : Nat) : Z0 := {lc(shapes[0])}
theorem entry : run0 table 1398 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (1882+54*n) (family n) = some (family (n+14)) := by
  have h := {join}
  rw [show {'+'.join('('+c+')' for c in costs)} = 1882+54*n by omega] at h
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append] using h
def invariant (z : Z0) : Prop := ∃ n, z = family n
theorem progress (z : Z0) (hz : invariant z) : ∃ t d, 0<t ∧ run0 table t z = some d ∧ invariant d := by
  obtain ⟨n,rfl⟩ := hz
  exact ⟨1882+54*n,_,by omega,growth n,n+14,rfl⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_progress table invariant 1398 (family 0) entry ⟨0,rfl⟩ progress m hm
#print axioms never
end BB6.Agent48D120
""")
(ROOT/"Agent48Raw61D120.lean").write_text("\n\n".join(out)+"\n")

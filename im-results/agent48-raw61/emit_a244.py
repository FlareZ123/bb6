"""Emit four-phase two-parameter proof for raw61 leaf 244."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
shared=ROOT.parent/"agent48-raw63-counter"/"emit_counter.py"
scope={"__file__":str(shared)}
exec(shared.read_text().split("\nTABLES=",1)[0],scope)
globals().update({k:v for k,v in scope.items() if not k.startswith("__") and k!="ROOT"})
p=tuple(parse("1RB0LE_1RC0LA_0RD1RB_1LD1RE_1RF0LB_0RC---"))
def shape(k,pre,m):
    r="001"*k
    return cfg(0,(),lit("00111"+r[:1])+repeat("010010","k")+lit(r[1:]+pre)+repeat("11","n")+lit("1"*m+"0000001"))
shapes=[shape(k,pre,m) for k,pre,m in [(18,"00000100",4),(20,"1110100",4),(21,"000001100",4),(23,"11001100",4),(24,"00000100",6)]]
out=["import Agent48CounterCore","namespace BB6.Agent48A244","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent48Counter","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",table(p)]
for i,(s,t,a) in enumerate(zip(shapes,shapes[1:],[293,317,327,393])):
    out.append(macro(p,f"stage{i}",s,t,("k","n"),(a,0,24))[0])
out.append(f"""
def family (k n : Nat) : Z0 := {lc(shapes[0])}
theorem entry : run0 table 2326 ⟨0,[],[]⟩ = some (family 0 0) := by rfl
theorem growth (k n : Nat) : run0 table (1330+96*k) (family k n) = some (family (k+3) (n+1)) := by
  have h := join0 (join0 (join0 (stage0 k n) (stage1 k n)) (stage2 k n)) (stage3 k n)
  rw [show (293+0*n+24*k)+(317+0*n+24*k)+(327+0*n+24*k)+(393+0*n+24*k)=1330+96*k by omega] at h
  simpa only [family,rep_right,List.append_assoc,List.cons_append,List.nil_append] using h
def invariant (z : Z0) : Prop := ∃ k n, z = family k n
theorem progress (z : Z0) (hz : invariant z) : ∃ t d, 0<t ∧ run0 table t z = some d ∧ invariant d := by
  obtain ⟨k,n,rfl⟩ := hz
  exact ⟨1330+96*k,_,by omega,growth k n,k+3,n+1,rfl⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_progress table invariant 2326 (family 0 0) entry ⟨0,0,rfl⟩ progress m hm
#print axioms never
end BB6.Agent48A244
""")
(ROOT/"Agent48Raw61A244.lean").write_text("\n\n".join(out)+"\n")

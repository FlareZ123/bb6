"""Generate multiphase raw61 witnesses 147 and 380."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
shared=ROOT.parent/"agent48-raw63-counter"/"emit_counter.py"
scope={"__file__":str(shared)}
exec(shared.read_text().split("\nTABLES=",1)[0],scope)
globals().update({k:v for k,v in scope.items() if not k.startswith("__") and k!="ROOT"})
out=["import Agent48CounterCore","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent48Counter","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false"]
p=tuple(parse("1RB0LE_1RC0LA_0RD---_1LD1RE_0RF0LB_0LB1RC"))
out+=["namespace BB6.Agent48A147",table(p)]
def A(k,m,s="",a=1,b=0):
    return cfg(0,(),lit("001"*a)+repeat("001"*4,"k")+lit("001"*(k-a)+"01"*b)+repeat("01"*2,"n")+lit("01"*(m-b)+s))
shapes=[A(3,4),A(4,5),A(5,3,"00100101"),A(6,2,"000010101"),A(7,6,"",5,2)]
for j,(st,tg,a) in enumerate(zip(shapes,shapes[1:],[108,144,128,126])):
    out.append(macro(p,f"stage{j}",st,tg,("k","n"),(a,24,56))[0])
out.append(f"""
def family (k n : Nat) : Z0 := {lc(shapes[0])}
theorem entry : run0 table 179 ⟨0,[],[]⟩ = some (family 0 0) := by rfl
theorem growth (k n : Nat) : run0 table (506+96*n+224*k) (family k n) = some (family (k+1) (n+1)) := by
  have h := join0 (join0 (join0 (stage0 k n) (stage1 k n)) (stage2 k n)) (stage3 k n)
  rw [show (108+24*n+56*k)+(144+24*n+56*k)+(128+24*n+56*k)+(126+24*n+56*k)=506+96*n+224*k by omega] at h
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append] using h
def invariant (z : Z0) : Prop := ∃ k n, z = family k n
theorem progress (z : Z0) (hz : invariant z) : ∃ t d, 0<t ∧ run0 table t z = some d ∧ invariant d := by
  obtain ⟨k,n,rfl⟩ := hz
  exact ⟨506+96*n+224*k,_,by omega,growth k n,k+1,n+1,rfl⟩
theorem live (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ invariant z :=
  arbitraryLive_of_progress table invariant 179 (family 0 0) entry ⟨0,0,rfl⟩ progress n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_progress table invariant 179 (family 0 0) entry ⟨0,0,rfl⟩ progress m hm
#print axioms never
end BB6.Agent48A147
""")
p=tuple(parse("1RB0LF_1RC0LA_0RD---_1LD1RE_1RC0LB_0RE1LF"))
out+=["namespace BB6.Agent48F380",table(p)]
st=cfg(5,(),lit("10001")+repeat("001","n"))
tg=cfg(5,(),lit("1"*11+"0001")+repeat("001","n"))
out.append(macro(p,"returnMacro",st,tg,("n",),(130,54,0))[0])
for m,a in [(11,49),(9,41),(7,33),(5,25),(3,17)]:
    out.append(f"theorem step{m} (S : List Bool) : run0 table {a} ⟨5,[],{bits('1'*m+'0001')}++S⟩ = some ⟨5,[],{bits('1'*(m-2)+'0001001')}++S⟩ := by rfl")
out.append("""
def family (n : Nat) : Z0 := ⟨5,[],[true,true,true,true,true,true,true,true,true,true,true,false,false,false,true] ++ rep [false,false,true] n⟩
theorem entry : run0 table 470 ⟨0,[],[]⟩ = some (family 3) := by rfl
theorem growth (n : Nat) : run0 table (165+130+54*(n+5)) (family n) = some (family (n+5)) := by
  let P := [false,false,true]
  have h1 := step11 (rep P n)
  have h2 := step9 (rep P (n+1))
  have h3 := step7 (rep P (n+2))
  have h4 := step5 (rep P (n+3))
  have h5 := step3 (rep P (n+4))
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have hh : run0 table 165 (family n) =
      some ⟨5,[],[true,false,false,false,true] ++ rep P (n+5)⟩ := by
    simpa only [family,P,rep,List.append_assoc,List.cons_append,List.nil_append] using h
  have h6 := returnMacro (n+5)
  have h7 := join0 hh h6
  rw [show 165+(130+54*(n+5))=165+130+54*(n+5) by omega] at h7
  exact h7
def invariant (z : Z0) : Prop := ∃ n, z = family n
theorem progress (z : Z0) (hz : invariant z) : ∃ t d, 0<t ∧ run0 table t z = some d ∧ invariant d := by
  obtain ⟨n,rfl⟩ := hz
  exact ⟨165+130+54*(n+5),_,by omega,growth n,n+5,rfl⟩
theorem live (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ invariant z :=
  arbitraryLive_of_progress table invariant 470 (family 3) entry ⟨3,rfl⟩ progress n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_progress table invariant 470 (family 3) entry ⟨3,rfl⟩ progress m hm
#print axioms never
end BB6.Agent48F380
""")
(ROOT/"Agent48Raw61Multiphase.lean").write_text("\n\n".join(out)+"\n")

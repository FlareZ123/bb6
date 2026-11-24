"""Generate five recursive unary counter proofs with arbitrary right tails."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
shared=ROOT.parent/"agent48-raw63-counter"/"emit_counter.py"
scope={"__file__":str(shared)}
exec(shared.read_text().split("\nTABLES=",1)[0],scope)
globals().update({k:v for k,v in scope.items() if not k.startswith("__") and k!="ROOT"})
P=repeat("1111","n")
S=repeat("X","S")
phases=[
 ("base",cfg(3,lit("00110"),S),cfg(3,lit("10110"),S),("n","S")),
 ("begin",cfg(3,lit("00111111")+P+lit("0"),S),cfg(3,lit("00110"),repeat("0000","n")+lit("0001")+S),("n","S")),
 ("cont",cfg(3,lit("1011")+P+lit("0"),lit("0000")+S),cfg(3,lit("00111111")+P+lit("0"),S),("n","S")),
 ("finish",cfg(3,lit("1011")+P+lit("0"),lit("0001")+S),cfg(3,lit("10111111")+P+lit("0"),S),("n","S")),
 ("grow",cfg(3,lit("1011")+P+lit("0"),()),cfg(3,lit("00111111")+P+lit("0"),()),("n",))]
tables={314:"1RB0LF_1RC0LA_0RD---_1LD1RE_0RC0LB_0RA0LA",
315:"1RB0LF_1RC0LA_0RD---_1LD1RE_0RC0LB_0RA0LE",
316:"1RB0LF_1RC0LA_0RD---_1LD1RE_0RC0LB_0RA0LF",
319:"1RB0LF_1RC0LA_0RD---_1LD1RE_0RC0LB_0RA1RD",
1085:"1RB1LF_1RC0LA_0RD---_1LD1RE_0RC0LB_0RF1RB"}
out=["import Agent48CounterCore","namespace BB6.Agent48RecursiveUnary","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent48Counter","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false"]
for i,s in tables.items():
    p=tuple(parse(s));out += [f"namespace M{i}",table(p)]
    a,b=(14,4) if i in (314,315,316) else (22,12)
    for (name,st,tg,params),expected in zip(phases,[(10,0,0),(a,b,0),(18,0,0),(18,0,0),(18,0,0)]):
        out.append(macro(p,name,st,tg,params,expected)[0])
    out.append(f"""
def F (n : Nat) (S : List Bool) : Z0 := ⟨3,[false,false,true,true] ++ rep [true,true,true,true] n ++ [false],S⟩
def G (n : Nat) (S : List Bool) : Z0 := ⟨3,[true,false,true,true] ++ rep [true,true,true,true] n ++ [false],S⟩
def zeros := [false,false,false,false]
def marker := [false,false,false,true]
theorem reachesJoin (x y z : Z0) : Reaches table x y → Reaches table y z → Reaches table x z := by
  rintro ⟨t,h⟩ ⟨u,h'⟩
  exact ⟨t+u,join0 h h'⟩
theorem baseR (S : List Bool) : Reaches table (F 0 S) (G 0 S) := by
  refine ⟨10,?_⟩
  exact base 0 S
theorem beginR (n : Nat) (S : List Bool) : Reaches table (F (n+1) S) (F 0 (rep zeros n ++ marker ++ S)) := by
  refine ⟨{a}+{b}*n,?_⟩
  simpa only [F,zeros,marker,rep,List.append_assoc,List.cons_append,List.nil_append] using begin n S
theorem contR (n : Nat) (S : List Bool) : Reaches table (G n (zeros ++ S)) (F (n+1) S) := by
  refine ⟨18,?_⟩
  simpa only [F,G,zeros,rep,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.add_zero] using cont n S
theorem finishR (n : Nat) (S : List Bool) : Reaches table (G n (marker ++ S)) (G (n+1) S) := by
  refine ⟨18,?_⟩
  simpa only [G,marker,rep,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.add_zero] using finish n S
theorem consume (k j : Nat) (S : List Bool)
    (h : ∀ m, m ≤ j+k → ∀ R, Reaches table (F m R) (G m R)) :
    Reaches table (G j (rep zeros k ++ marker ++ S)) (G (j+k+1) S) := by
  induction k generalizing j with
  | zero => simpa [rep] using finishR j S
  | succ k ih =>
    have h1 := contR j (rep zeros k ++ marker ++ S)
    have h2 := h (j+1) (by omega) (rep zeros k ++ marker ++ S)
    have h3 := ih (j+1) (by
      intro m hm
      exact h m (by omega))
    have hh := reachesJoin _ _ _ (reachesJoin _ _ _ h1 h2) h3
    rw [show j+1+k+1=j+(k+1)+1 by omega] at hh
    simpa only [rep,List.append_assoc] using hh
theorem completeUpTo (n : Nat) : ∀ m, m ≤ n → ∀ S, Reaches table (F m S) (G m S) := by
  induction n with
  | zero =>
    intro m hm S
    have he : m = 0 := by omega
    subst m
    exact baseR S
  | succ n ih =>
    intro m hm S
    by_cases h : m ≤ n
    · exact ih m h S
    · have he : m = n+1 := by omega
      subst m
      have h1 := beginR n S
      have h2 := baseR (rep zeros n ++ marker ++ S)
      have h3 := consume n 0 S (by
        intro j hj R
        exact ih j (by omega) R)
      simp only [Nat.zero_add] at h3
      exact reachesJoin _ _ _ (reachesJoin _ _ _ h1 h2) h3
theorem complete (n : Nat) (S : List Bool) : Reaches table (F n S) (G n S) :=
  completeUpTo n n (by omega) S
theorem entry : run0 table 31 ⟨0,[],[]⟩ = some (F 1 []) := by rfl
def invariant (z : Z0) : Prop := ∃ n, z = F n []
theorem progress (z : Z0) (hz : invariant z) : ∃ t d, 0 < t ∧ run0 table t z = some d ∧ invariant d := by
  obtain ⟨n,rfl⟩ := hz
  obtain ⟨t,ht⟩ := complete n []
  have h2 : run0 table 18 (G n []) = some (F (n+1) []) := by
    simpa only [F,G,rep,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.add_zero] using grow n
  exact ⟨t+18,F (n+1) [],by omega,join0 ht h2,n+1,rfl⟩
theorem live (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ invariant z :=
  arbitraryLive_of_progress table invariant 31 (F 1 []) entry ⟨1,rfl⟩ progress n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_progress table invariant 31 (F 1 []) entry ⟨1,rfl⟩ progress m hm
#print axioms never
end M{i}""")
out.append("end BB6.Agent48RecursiveUnary")
(ROOT/"Agent48Raw61RecursiveUnary.lean").write_text("\n\n".join(out)+"\n")

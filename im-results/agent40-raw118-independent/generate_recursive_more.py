"""Eight additional exact instances of nested restoration, generated without simulation or search."""
from generate_independent import tab
from independent import parse

# id, table, growth stride, blank entry cost, pref cost, advance cost
CASES=[
 (3963,"1RB---_1RC0RA_0RD1RA_1LD1RE_1LF0LE_0RB0LA",5,24,17,9),
 (3964,"1RB---_1RC0RA_0RD1RB_1LD1RE_1LF0LE_0RB0LA",4,23,17,8),
 (3965,"1RB---_1RC0RA_0RD1RC_1LD1RE_1LF0LE_0RB0LA",3,22,17,7),
 (3976,"1RB0LA_1RC0RA_0RD---_1LD1RE_1LF0LE_0RB1LA",3,24,17,9),
 (3978,"1RB---_1RC0RA_0RD1RC_1LD1RE_1LF0LE_0RB1LB",3,22,17,7),
 (4094,"1RB---_1RC1RB_0RD0RA_1LD1RE_1LF0LE_0RC1LA",4,23,17,8),
 (4095,"1RB0LA_1RC---_0RD0RA_1LD1RE_1LF0LE_0RC1LB",3,24,17,9),
 (4096,"1RB0LB_1RC---_0RD0RA_1LD1RE_1LF0LE_0RC1LB",2,23,17,8),
]
def emit(i,s,g,entry,pref,adv):
    # The exact source computations are checked by Lean, not trusted constants.
    post=4
    return f'''namespace M{i}
-- {s}
{tab(parse(s))}

theorem reset_aux (k : Nat) (R : List Bool) :
    run0 table (3+k+{post})
      ⟨3,[false,false,true,true] ++ List.replicate k true ++ [false,false],R⟩ =
    some ⟨5,[false],[true,false,false,false] ++ List.replicate k false ++ true::R⟩ := by
  have h1 : run0 table 3 ⟨3,[false,false,true,true] ++ List.replicate k true ++ [false,false],R⟩ =
      some ⟨4,[true,true,true] ++ List.replicate k true ++ [false,false],true::R⟩ := by rfl
  have h2 := sweepL table 4 [true,true,true] [] [true] [false] 1 (by intro L R; rfl) k [false,false] (true::R)
  have h2' : run0 table k ⟨4,[true,true,true] ++ List.replicate k true ++ [false,false],true::R⟩ =
      some ⟨4,[true,true,true,false,false],List.replicate k false ++ true::R⟩ := by
    simpa only [Nat.one_mul,rep_singleton,List.nil_append,List.cons_append] using h2
  have h3 : run0 table {post} ⟨4,[true,true,true,false,false],List.replicate k false ++ true::R⟩ =
      some ⟨5,[false],[true,false,false,false] ++ List.replicate k false ++ true::R⟩ := by rfl
  exact join0 (join0 h1 h2') h3

theorem reset (n : Nat) (R : List Bool) : PositiveRun table (D {g} false n R) (FStart (Z ({g}*n+3) ++ true::R)) := by
  refine ⟨3+{g}*n+{post},by omega,?_⟩
  have h := reset_aux ({g}*n) R
  simpa only [D,FStart,Z,List.replicate_succ,List.cons_append,List.nil_append,List.append_assoc] using h

theorem seed (R : List Bool) : PositiveRun table (FStart (Z 3 ++ true::R)) (D {g} true 0 R) :=
  ⟨5,by decide,by rfl⟩

theorem pref (R : List Bool) : PositiveRun table (FStart (Z 4 ++ R)) (D {g} true 0 R) :=
  ⟨{pref},by decide,by rfl⟩

theorem advance (b : Bool) (n : Nat) (R : List Bool) :
    PositiveRun table (D {g} true n (Z ({g}-1) ++ b::R)) (D {g} b (n+1) R) := by
  refine ⟨{adv},by decide,?_⟩
  unfold D
  rw [show {g}*(n+1)+2 = {g}+({g}*n+2) by omega, ← (List.replicate_append_replicate (n := {g}) (m := {g}*n+2) (a := true))]
  cases b <;> rfl

theorem blank (n : Nat) : PositiveRun table (D {g} true n []) (D {g} false (n+1) []) := by
  refine ⟨{adv},by decide,?_⟩
  unfold D
  rw [show {g}*(n+1)+2 = {g}+({g}*n+2) by omega, ← (List.replicate_append_replicate (n := {g}) (m := {g}*n+2) (a := true))]
  rfl

def Inv (z : Z0) : Prop := ∃ n, z = D {g} false n []
theorem entry : ∃ t z, run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z :=
  ⟨{entry},D {g} false 1 [],by rfl,⟨1,rfl⟩⟩
theorem closed : ∀ z, Inv z → ∃ k z', 0 < k ∧ run0 table k z = some z' ∧ Inv z' := by
  rintro z ⟨n,rfl⟩
  obtain ⟨k,hk,h⟩ := growing_from table {g} (by decide) FStart reset seed pref advance blank n
  exact ⟨k,D {g} false (n+1) [],hk,h,⟨n+1,rfl⟩⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_closed table Inv entry closed m hm
#print axioms never
end M{i}
'''

if __name__=='__main__':
    print('import RecursiveCounterCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6Coverage.Agent40Recursive.Raw118More\nopen BB6Coverage Agent31Pump Agent40Independent Agent40Recursive\n\ndef FStart (R : List Bool) : Z0 := ⟨5,[false],true::R⟩\n\ntheorem rep_singleton (b : Bool) (n : Nat) : rep [b] n = List.replicate n b := by\n  induction n with\n  | zero => rfl\n  | succ n ih => simp [rep,List.replicate_succ,ih]')
    for case in CASES:print(emit(*case))
    print('end BB6Coverage.Agent40Recursive.Raw118More')

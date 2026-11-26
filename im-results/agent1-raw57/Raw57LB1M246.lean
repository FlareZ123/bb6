import SweepPumping
namespace BB6Coverage.Agent7Raw57LB1M246
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- 1RB1LB_1RC0LF_0RD0RC_1LD1RE_1RC0LA_0LA---
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
abbrev P : List Bool := [false,true,false]
abbrev Q : List Bool := [true,true,false]
abbrev J : List Bool := [false,false,true]
abbrev U : List Bool := [true]
abbrev Z : List Bool := [false]
def family (n : Nat) : Z0 := ⟨5,[],P++rep P n++U++rep U n⟩
theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem s0 (n : Nat) : run0 table 3 (family n) = some ⟨2,[false,true,true],[true,false]++rep P n++U++rep U n⟩ := by rfl
theorem s1 (n : Nat) : run0 table (3*n) ⟨2,[false,true,true],[true,false]++rep P n++U++rep U n⟩ = some ⟨2,[false]++rep Q n++[true,true],[true,false,true]++rep U n⟩ := by
  have h := sweepR table 2 [false] [true,false] P Q 3 (by intro L R; rfl) n [true,true] (U++rep U n)
  simp only [List.append_assoc] at h ⊢
  exact h
theorem s2 (n : Nat) : run0 table 3 ⟨2,[false]++rep Q n++[true,true],[true,false,true]++rep U n⟩ = some ⟨2,[true,true,true,false]++rep Q n++[true,true],rep U n⟩ := by rfl
theorem s3 (n : Nat) : run0 table (1*n) ⟨2,[true,true,true,false]++rep Q n++[true,true],rep U n⟩ = some ⟨2,[true]++rep Z n++Q++rep Q n++[true,true],[]⟩ := by
  have h := sweepR table 2 [true] [] U Z 1 (by intro L R; rfl) n (Q++rep Q n++[true,true]) []
  simp only [List.append_assoc,List.append_nil] at h ⊢
  exact h
theorem s4 (n : Nat) : run0 table 2 ⟨2,[true]++rep Z n++Q++rep Q n++[true,true],[]⟩ = some ⟨3,[false,false,false]++rep Z n++Q++rep Q n++[true,true],[]⟩ := by rfl
theorem s5 (n : Nat) : run0 table (1*n) ⟨3,[false,false,false]++rep Z n++Q++rep Q n++[true,true],[]⟩ = some ⟨3,[false,false,false]++Q++rep Q n++[true,true],rep U n⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append] using sweepL table 3 [false,false,false] [] Z U 1 (by intro L R; rfl) n (Q++rep Q n++[true,true]) []
theorem s6 (n : Nat) : run0 table 5 ⟨3,[false,false,false]++Q++rep Q n++[true,true],rep U n⟩ = some ⟨0,Q++rep Q n++[true,true],[false,true,true]++rep U n⟩ := by rfl
theorem s7 (n : Nat) : run0 table (3*n) ⟨0,Q++rep Q n++[true,true],[false,true,true]++rep U n⟩ = some ⟨0,Q++[true,true],rep J n++[false,true,true]++rep U n⟩ := by
  simpa only [List.append_assoc,List.nil_append] using sweepL table 0 Q [] Q J 3 (by intro L R; rfl) n [true,true] ([false,true,true]++rep U n)
theorem s8 (n : Nat) : run0 table 5 ⟨0,Q++[true,true],rep J n++[false,true,true]++rep U n⟩ = some ⟨5,[],[false,true,false,false,true]++rep J n++[false,true,true]++rep U n⟩ := by rfl
theorem final_word (n : Nat) : [false,true,false,false,true]++rep J n++[false,true,true]++rep U n = P++rep P (n+1)++U++rep U (n+1) := by
  -- Rotate the last 0 of the target prefix through (010)^n.
  have e := moveCut [false,true,false,false,true] ([true,true]++rep U n) [false,true] false n
  simp only [rep,List.append_assoc] at e ⊢
  exact e.symm

theorem growth (n : Nat) : run0 table (18+8*n) (family n) = some (family (n+1)) := by
  have h := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (s0 n) (s1 n)) (s2 n)) (s3 n)) (s4 n)) (s5 n)) (s6 n)) (s7 n)) (s8 n)
  rw [final_word n] at h
  rw [show 3+3*n+3+1*n+2+1*n+5+3*n+5=18+8*n by omega] at h
  exact h
#print axioms entry
#print axioms growth
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 (fun n => 18+8*n) entry (by intro n; omega) growth m hm
#print axioms never
end BB6Coverage.Agent7Raw57LB1M246

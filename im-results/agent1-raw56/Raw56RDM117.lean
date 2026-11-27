import UnarySweep
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent1Raw56RDM117
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent1UnarySweep

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def Good (a : Nat) (c : Bool) (b : Nat) : Prop :=
  if c then (a%5=3 ∨ a%5=4) ∧ b%5=4 ∧ 4≤b else 1≤b ∧ ( (a+b)%5=4 ∨ (a+b)%5=0 )

theorem bscan (a n : Nat) : run0 table n ⟨1,true :: List.replicate a true,List.replicate n true⟩ =
    some ⟨1,true :: List.replicate (a+n) true,[]⟩ := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [run0.eq_2]
    change run0 table n ⟨1,true :: List.replicate (a+1) true,List.replicate n true⟩ = _
    rw [show a+n.succ = (a+1)+n by omega]
    exact ih (a+1)

theorem right (a b : Nat) : Macro table (b+12) a false (b+1) (a+b) true 4 := by
  apply macro_exact
  have h1 : run0 table 1 (AConfig a false (b+1)) = some ⟨1,true :: List.replicate (a+1) true,List.replicate b true⟩ := by rfl
  have h2 := bscan (a+1) b
  have h3 : run0 table 1 ⟨1,true :: List.replicate ((a+1)+b) true,[]⟩ = some ⟨1,false :: List.replicate (a+b+2) true,[]⟩ := by
    rw [show a+b+2 = (a+1)+b+1 by omega]
    rfl
  have h4 : run0 table 10 ⟨1,false :: List.replicate (a+b+2) true,[]⟩ = some (AConfig (a+b) true 4) := by rfl
  rw [show b+12=1+b+1+10 by omega]
  exact join0 (join0 (join0 h1 h2) h3) h4

theorem left (a b : Nat) : Macro table 13 (a+5) true b a true (b+5) := by
  apply macro_exact; rfl

theorem end3 (b : Nat) : Macro table 10 3 true b 0 false (b+6) := by
  apply macro_blankLeft; rfl

theorem end4 (b : Nat) : Macro table 13 4 true b 0 false (b+5) := by
  apply macro_blankLeft; rfl

theorem closed (a : Nat) (c : Bool) (b : Nat) (h : Good a c b) :
    ∃ k A C B, 0 < k ∧ Macro table k a c b A C B ∧ Good A C B := by
  cases c with
  | false =>
    change 1≤b ∧ ((a+b)%5=4 ∨ (a+b)%5=0) at h
    obtain ⟨j,rfl⟩ : ∃ j, b=j+1 := ⟨b-1,by omega⟩
    exact ⟨j+12,a+j,true,4,by omega,right a j,by change ((a+j)%5=3 ∨ (a+j)%5=4) ∧ 4%5=4 ∧ 4≤4; omega⟩
  | true =>
    change (a%5=3 ∨ a%5=4) ∧ b%5=4 ∧ 4≤b at h
    by_cases ha : a=3
    · subst a
      exact ⟨10,0,false,b+6,by decide,end3 b,by change 1≤b+6 ∧ ((0+(b+6))%5=4 ∨ (0+(b+6))%5=0); omega⟩
    · by_cases ha2 : a=4
      · subst a
        exact ⟨13,0,false,b+5,by decide,end4 b,by change 1≤b+5 ∧ ((0+(b+5))%5=4 ∨ (0+(b+5))%5=0); omega⟩
      · obtain ⟨j,rfl⟩ : ∃ j, a=j+5 := ⟨a-5,by omega⟩
        exact ⟨13,j,true,b+5,by decide,left j b,by change (j%5=3 ∨ j%5=4) ∧ (b+5)%5=4 ∧ 4≤b+5; omega⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_macros table Good _ closed m hm
  refine ⟨11,⟨0,[],[true,true,true,true]⟩,0,false,4,by decide,rfl,?_,by unfold Good; decide⟩
  exact ⟨rfl,pad_symm pad_false_nil,pad_refl _⟩
#print axioms never
end BB6Coverage.Agent1Raw56RDM117

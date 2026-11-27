import UnarySweep
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent1Raw56RDM109
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent1UnarySweep

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def Good (a : Nat) (c : Bool) (b : Nat) : Prop :=
  if c then a%2=1 ∧ b%2=0 ∧ 6≤b else 3≤b ∧ (a+b)%2=0

theorem right (a b : Nat) : Macro table 7 a false (b+4) (a+1) false (b+3) := by
  apply macro_exact; rfl

theorem turn1 : Macro table 14 1 false 3 0 false 6 := by
  apply macro_blankLeft; rfl

theorem turn (a : Nat) : Macro table 14 (a+3) false 3 (a+1) true 6 := by
  apply macro_exact; rfl

theorem left (a b : Nat) : Macro table 4 (a+3) true b (a+1) true (b+2) := by
  apply macro_exact; rfl

theorem endLeft (b : Nat) : Macro table 4 1 true b 0 false (b+2) := by
  apply macro_blankLeft; rfl

theorem closed (a : Nat) (c : Bool) (b : Nat) (h : Good a c b) :
    ∃ k A C B, 0 < k ∧ Macro table k a c b A C B ∧ Good A C B := by
  cases c with
  | false =>
    change 3≤b ∧ (a+b)%2=0 at h
    by_cases hb : b=3
    · subst b
      by_cases ha : a=1
      · subst a; exact ⟨14,0,false,6,by decide,turn1,by unfold Good; decide⟩
      · obtain ⟨j,rfl⟩ : ∃ j, a=j+3 := ⟨a-3,by omega⟩
        exact ⟨14,j+1,true,6,by decide,turn j,by change (j+1)%2=1 ∧ 6%2=0 ∧ 6≤6; omega⟩
    · obtain ⟨j,rfl⟩ : ∃ j, b=j+4 := ⟨b-4,by omega⟩
      exact ⟨7,a+1,false,j+3,by decide,right a j,by change 3≤j+3 ∧ (a+1+(j+3))%2=0; omega⟩
  | true =>
    change a%2=1 ∧ b%2=0 ∧ 6≤b at h
    by_cases ha : a=1
    · subst a
      exact ⟨4,0,false,b+2,by decide,endLeft b,by change 3≤b+2 ∧ (0+(b+2))%2=0; omega⟩
    · obtain ⟨j,rfl⟩ : ∃ j, a=j+3 := ⟨a-3,by omega⟩
      exact ⟨4,j+1,true,b+2,by decide,left j b,by change (j+1)%2=1 ∧ (b+2)%2=0 ∧ 6≤b+2; omega⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_macros table Good _ closed m hm
  refine ⟨11,⟨0,[],[true,true,true,true]⟩,0,false,4,by decide,rfl,?_,by unfold Good; decide⟩
  exact ⟨rfl,pad_symm pad_false_nil,pad_refl _⟩
#print axioms never
end BB6Coverage.Agent1Raw56RDM109

import UnarySweep
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent1Raw56LEM111
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent1UnarySweep

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def Good (a : Nat) (c : Bool) (b : Nat) : Prop :=
  if c then a%3≠0 ∧ b%3=0 ∧ 3≤b else 2≤b ∧ (a+b)%3≠2

theorem right (a b : Nat) : Macro table 7 a false (b+3) (a+1) false (b+2) := by
  apply macro_exact; rfl

theorem turn (a : Nat) : Macro table 6 a false 2 a true 3 := by
  apply macro_exact; rfl

theorem left (a b : Nat) : Macro table 7 (a+3) true b a true (b+3) := by
  apply macro_exact; rfl

theorem end1 (b : Nat) : Macro table 5 1 true b 0 false (b+3) := by
  apply macro_blankLeft; rfl

theorem end2 (b : Nat) : Macro table 7 2 true b 0 false (b+3) := by
  apply macro_blankLeft; rfl

theorem closed (a : Nat) (c : Bool) (b : Nat) (h : Good a c b) :
    ∃ k A C B, 0 < k ∧ Macro table k a c b A C B ∧ Good A C B := by
  cases c with
  | false =>
    change 2≤b ∧ (a+b)%3≠2 at h
    by_cases hb : b=2
    · subst b
      exact ⟨6,a,true,3,by decide,turn a,by change a%3≠0 ∧ 3%3=0 ∧ 3≤3; omega⟩
    · obtain ⟨j,rfl⟩ : ∃ j, b=j+3 := ⟨b-3,by omega⟩
      exact ⟨7,a+1,false,j+2,by decide,right a j,by change 2≤j+2 ∧ (a+1+(j+2))%3≠2; omega⟩
  | true =>
    change a%3≠0 ∧ b%3=0 ∧ 3≤b at h
    by_cases ha : a=1
    · subst a
      exact ⟨5,0,false,b+3,by decide,end1 b,by change 2≤b+3 ∧ (0+(b+3))%3≠2; omega⟩
    · by_cases ha2 : a=2
      · subst a
        exact ⟨7,0,false,b+3,by decide,end2 b,by change 2≤b+3 ∧ (0+(b+3))%3≠2; omega⟩
      · obtain ⟨j,rfl⟩ : ∃ j, a=j+3 := ⟨a-3,by omega⟩
        exact ⟨7,j,true,b+3,by decide,left j b,by change j%3≠0 ∧ (b+3)%3=0 ∧ 3≤b+3; omega⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_macros table Good _ closed m hm
  refine ⟨9,⟨0,[],[true,true,true,true]⟩,0,false,4,by decide,rfl,?_,by unfold Good; decide⟩
  exact ⟨rfl,pad_symm pad_false_nil,pad_refl _⟩
#print axioms never
end BB6Coverage.Agent1Raw56LEM111

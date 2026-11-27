import Raw63ParentCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw63
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent10Raw63

/-- 1RB0LA_1RC1LA_0RD0RF_1LD1RE_HHH0LB_0RC1LA. -/
def attainingMachine : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,false,0⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,false,0⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨false,true,5⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,true,4⟩
  | 4,false => none
  | 4,true => some ⟨false,false,1⟩
  | 5,false => some ⟨false,true,2⟩
  | 5,true => some ⟨true,false,0⟩
  | _,_ => none

theorem attainingCompatible : compatible p63 attainingMachine := by
  rw [parent_eq_literal]
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | exact Option.some.inj ht | contradiction

theorem attainingHalts : HaltsAfter attainingMachine 357 := by
  constructor
  · rfl
  · rfl

theorem attainingDelay : 0 ∈ delays (zeroNext attainingMachine) 0 := by decide

/-- Exact threshold, not merely a sufficient upper bound. -/
theorem exact_weighted_threshold (B : Nat) :
    (∀ m, compatible p63 m → WeightedBound B m) ↔ 358 ≤ B := by
  constructor
  · intro h
    exact h attainingMachine attainingCompatible 357 0 attainingHalts attainingDelay
  · intro h m hm k d hk hd
    exact Nat.le_trans (all63 m hm k d hk hd) h

theorem exact_literal_threshold (B : Nat) :
    (∀ m, compatible literalParent m → WeightedBound B m) ↔ 358 ≤ B := by
  rw [← parent_eq_literal]
  exact exact_weighted_threshold B

#print axioms attainingCompatible
#print axioms attainingHalts
#print axioms attainingDelay
#print axioms exact_weighted_threshold
#print axioms exact_literal_threshold
end BB6.Agent2Raw63

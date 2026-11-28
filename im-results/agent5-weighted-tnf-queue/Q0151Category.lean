import Q0151ResidueSemantics

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151Category
open BB6.Agent5Q0151ResidueSemantics

/-!
Category normalization for unbounded right-hand run lengths.
The finite abstract search retains exact lengths 1..4 and encodes every
larger length by 5+(n-1)%4, i.e. one of 5,6,7,8.
-/

def cat (n : Nat) : Nat :=
  if n ≤ 4 then n else 5 + (n - 1) % 4

theorem cat_mod (n : Nat) : cat n % 4 = n % 4 := by
  by_cases h : n ≤ 4
  · simp [cat,h]
  · simp only [cat,if_neg h]
    omega

theorem cat_idempotent (n : Nat) : cat (cat n) = cat n := by
  by_cases h : n ≤ 4
  · simp [cat,h]
  · have hh : ¬ (5 + (n-1)%4 ≤ 4) := by omega
    simp only [cat,if_neg h,if_neg hh]
    omega

theorem gateStep_cat (mode : Bool) (n : Nat) :
    gateStep mode (cat n) = gateStep mode n := by
  simp only [gateStep,cat_mod]

theorem gateRun_cats (mode : Bool) (xs : List Nat) :
    gateRun mode (xs.map cat) = gateRun mode xs := by
  induction xs generalizing mode with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.map_cons,gateRun,gateStep_cat]
    cases h : gateStep mode n with
    | none => simp [h]
    | some mode' => simpa [h] using ih mode'

theorem gateMask_cats (xs : List Nat) :
    gateMask (xs.map cat) = gateMask xs := by
  simp only [gateMask,gateRun_cats]

#print axioms cat_mod
#print axioms cat_idempotent
#print axioms gateRun_cats
#print axioms gateMask_cats
end BB6.Agent5Q0151Category

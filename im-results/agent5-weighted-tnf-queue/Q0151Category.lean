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

/-! Category addition is a congruence: this is the algebraic obligation
needed to abstract the merger of an unfinished segment run with the first
run on the right. -/

theorem cat_small (n : Nat) (h : n ≤ 4) : cat n = n := by
  simp [cat, h]

theorem cat_large (n : Nat) (h : 5 ≤ n) : 5 ≤ cat n := by
  have hn : ¬ n ≤ 4 := by omega
  simp only [cat, if_neg hn]
  omega

theorem cat_eq_of_large_mod (a b : Nat)
    (ha : 5 ≤ a) (hb : 5 ≤ b) (hm : a % 4 = b % 4) :
    cat a = cat b := by
  have hna : ¬ a ≤ 4 := by omega
  have hnb : ¬ b ≤ 4 := by omega
  simp only [cat, if_neg hna, if_neg hnb]
  omega

theorem cat_add (a b : Nat) :
    cat (cat a + cat b) = cat (a + b) := by
  by_cases hsmall : a + b ≤ 4
  · have ha : a ≤ 4 := by omega
    have hb : b ≤ 4 := by omega
    rw [cat_small a ha, cat_small b hb]
  · have hlarge : 5 ≤ a + b := by omega
    have hs : 5 ≤ cat a + cat b := by
      by_cases ha : a ≤ 4
      · by_cases hb : b ≤ 4
        · rw [cat_small a ha, cat_small b hb]
          omega
        · have hcb : 5 ≤ cat b := cat_large b (by omega)
          rw [cat_small a ha]
          omega
      · have hca : 5 ≤ cat a := cat_large a (by omega)
        omega
    have hm : (cat a + cat b) % 4 = (a + b) % 4 := by
      have ha := cat_mod a
      have hb := cat_mod b
      omega
    exact cat_eq_of_large_mod (cat a + cat b) (a + b) hs hlarge hm

#print axioms cat_mod
#print axioms cat_idempotent
#print axioms cat_add
#print axioms gateRun_cats
#print axioms gateMask_cats
end BB6.Agent5Q0151Category

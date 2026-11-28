import Q0151Category
import Q0151FiniteModel

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151RunAddition
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151FiniteModel

/-!
Proof that the abstract open-run merge `plus` agrees with ordinary addition
after applying `cat`. This is a necessary soundness bridge for concatenating
a physical current segment and the right tape.
-/

theorem plus_normalized (a b : Nat)
    (ha : cat a = a) (hb : cat b = b) :
    plus a b = cat (a+b) := by
  by_cases h0 : a = 0
  · subst a
    simpa [plus] using hb.symm
  · by_cases h1 : b = 0
    · subst b
      simpa [plus,h0] using ha.symm
    · by_cases hs : a+b ≤ 4
      · simp [plus,h0,h1,cat,hs]
      · simp [plus,h0,h1,cat,hs]

theorem plus_cat (a b : Nat) :
    plus (cat a) (cat b) = cat (a+b) := by
  rw [plus_normalized (cat a) (cat b) (cat_idempotent a)
      (cat_idempotent b),cat_add]

theorem cat_is_valid (a : Nat) : cat (cat a) = cat a :=
  cat_idempotent a

#print axioms plus_normalized
#print axioms plus_cat
end BB6.Agent5Q0151RunAddition

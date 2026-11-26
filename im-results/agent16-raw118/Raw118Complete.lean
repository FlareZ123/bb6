import Raw118Consumer
import Raw118M2869

namespace BB6.Agent1Raw118Complete
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16ResidualCover

theorem holdout_eq :
    BB6.Agent16Raw118Consumer.holdout = BB6Coverage.Agent1Raw118M2869.table :=
  sameTable_sound (by decide : sameTable BB6.Agent16Raw118Consumer.holdout BB6Coverage.Agent1Raw118M2869.table = true)

theorem holdout_cover (B : Nat) :
    Cover (WeightedBound B) BB6.Agent16Raw118Consumer.holdout := by
  refine Cover.leaf _ ?_
  intro m hm
  rw [holdout_eq] at hm
  exact weighted_never B m (BB6Coverage.Agent1Raw118M2869.never m hm)

/-- All compatible completions have the sharp weighted bound. -/
theorem parent_cover :
    Cover (WeightedBound BB6.Agent16Raw118.bound) BB6.Agent16Raw118.parent :=
  BB6.Agent16Raw118Consumer.parent_cover_at_target (Nat.le_refl _)
    (holdout_cover BB6.Agent16Raw118.bound)

theorem parent_cover_monotone {B : Nat} (hB : BB6.Agent16Raw118.bound ≤ B) :
    Cover (WeightedBound B) BB6.Agent16Raw118.parent :=
  BB6.Agent16Raw118Consumer.parent_cover_at_target hB (holdout_cover B)

theorem parent_exact :
    Cover (WeightedBound BB6.Agent16Raw118.bound) BB6.Agent16Raw118.parent ∧
    ∀ B, Cover (WeightedBound B) BB6.Agent16Raw118.parent → BB6.Agent16Raw118.bound ≤ B :=
  BB6.Agent16Raw118Consumer.parent_exact_if_holdout
    (holdout_cover BB6.Agent16Raw118.bound)

#print axioms holdout_cover
#print axioms parent_cover
#print axioms parent_exact
end BB6.Agent1Raw118Complete

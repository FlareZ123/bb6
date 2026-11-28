import Raw39SiblingThreshold
import Raw39Canonical40Conditional

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
An exact original-source global conditional with only the single unsolved Raw39
A1=1LE child in addition to the 39 other Canonical40 quotient representatives.
This file does *not* establish that the 1LE child is bounded; that final
hypothesis must be discharged by the complete source-checked 1LE proof.
-/-

namespace BB6.Agent11Raw39SoleObligation

open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6ChampionArithmetic

abbrev p39 : PartialMachine := BB6.Agent11Raw39Canonical40Membership.p
abbrev oneLE : PartialMachine :=
  BB6.Agent11Raw39AcceptedSix.child ⟨true,false,4⟩

theorem literal_source_equality :
    p39 = BB6.Agent11Raw39AcceptedSix.p39 :=
  sameTable_sound (by decide)

theorem parent_bound_of_oneLE (h1 : Bound 28311 oneLE) :
    Bound 28311 p39 := by
  rw [literal_source_equality]
  exact BB6.Agent11Raw39TenChild.conditional_parent_bound h1

theorem parent_cover_of_oneLE (h1 : Bound 28311 oneLE) :
    Cover (WeightedBound 6766859) p39 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (parent_bound_of_oneLE h1 m hm k d hk hd)
    (by decide : 28311 ≤ 6766859)

/-- The 40-cover global proof is factored into the original 1LE first-hole
completion and the 39 exact remaining quotient representatives. -/
/-- A direct source-certified sibling join applies at ANY threshold
above the largest remaining sibling bound 15125, requiring the complete 1LE
child only at that threshold. No all-threshold equivalence is needed. -/
theorem parent_cover_if_oneLE_above_15125 (B : Nat) (hB : 15125 ≤ B)
    (h1 : Bound B oneLE) : Cover (WeightedBound B) p39 := by
  rw [literal_source_equality]
  exact BB6.Agent11Raw39SiblingThreshold.cover_from_oneLE B hB h1

/-- At the global quotient's accepted intermediate score, the only Raw39
hypothesis needed is the A1=1LE child at that *same* score. -/
theorem parent_cover_if_oneLE_at_global
    (h1 : Bound 6766859 oneLE) :
    Cover (WeightedBound 6766859) p39 :=
  parent_cover_if_oneLE_above_15125 6766859 (by decide) h1

theorem exact_at_champion_if_oneLE_at_global
    (h1 : Bound 6766859 oneLE)
    (hRest : ∀ e ∈ BB6.Agent11Raw39Canonical40Conditional.roster39,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent11Raw39Canonical40Conditional.conditional_exact_at_champion
    (parent_cover_if_oneLE_at_global h1) hRest

theorem exact_at_champion_if_oneLE
    (h1 : Bound 28311 oneLE)
    (hRest : ∀ e ∈ BB6.Agent11Raw39Canonical40Conditional.roster39,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent11Raw39Canonical40Conditional.conditional_exact_at_champion
    (parent_cover_of_oneLE h1) hRest

#print axioms literal_source_equality
#print axioms parent_bound_of_oneLE
#print axioms parent_cover_of_oneLE
#print axioms parent_cover_if_oneLE_above_15125
#print axioms parent_cover_if_oneLE_at_global
#print axioms exact_at_champion_if_oneLE_at_global
#print axioms exact_at_champion_if_oneLE

end BB6.Agent11Raw39SoleObligation

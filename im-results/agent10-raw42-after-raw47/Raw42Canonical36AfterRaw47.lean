import Raw42AfterCanonical37Conditional
import Raw42AcceptedParent

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Final Raw42 global successor target after the authenticated Raw39 -> Raw112 ->
Raw47 Canonical37 lineage.  This module becomes an accepted 37 -> 36 reduction
only when compiled in one authenticated kernel closure containing both the
Canonical37 predecessor and the independently source-accepted twelve-child
Raw42 parent Cover.
-/

namespace BB6.Agent10Raw42Canonical36AfterRaw47

open BB6Coverage BB6.Agent13BlankDelay
open BB6ChampionArithmetic

abbrev p42 : PartialMachine :=
  BB6.Agent10Raw42AfterCanonical37Conditional.p42

noncomputable abbrev roster36 :=
  BB6.Agent10Raw42AfterCanonical37Conditional.roster36

theorem literal_eq_accepted_parent :
    p42 = BB6.Agent17Raw42GlobalBridge.literal := by
  rfl

theorem p42_cover :
    Cover (WeightedBound 6766859) p42 := by
  rw [literal_eq_accepted_parent]
  exact BB6.Agent17Raw42AcceptedParent.cover_global

theorem count36 : roster36.length = 36 :=
  BB6.Agent10Raw42AfterCanonical37Conditional.count36

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m :=
  BB6.Agent10Raw42AfterCanonical37Conditional.conditional_sound p42_cover

theorem sound_at (B : Nat) (hFloor : 6766859 ≤ B) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound_integrated m hm with hsmall | hrest
  · exact Or.inl (fun k d hk hd =>
      Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster36,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent10Raw42AfterCanonical37Conditional.conditional_exact_at_champion
    p42_cover hLeaves

#print axioms literal_eq_accepted_parent
#print axioms p42_cover
#print axioms count36
#print axioms sound_integrated
#print axioms sound_at
#print axioms exact_at_champion_score

end BB6.Agent10Raw42Canonical36AfterRaw47

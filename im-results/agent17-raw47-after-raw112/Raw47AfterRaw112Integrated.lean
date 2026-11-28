import Raw47AfterRaw112Conditional
import Raw47Complete

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Unconditional Raw47 successor of the source-accepted Raw112-first Canonical38.

The predecessor is the exact Raw39 -> Raw112 roster38.  Raw47 is checked by
the conditional module to occur exactly once in that roster.  This bridge
identifies that literal parent with the independently source-accepted Raw47
whole-parent theorem, discharging the only remaining premise and yielding an
exact 37-representative quotient.
-/

namespace BB6.Agent17Raw47AfterRaw112Integrated

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p47 : PartialMachine :=
  BB6.Agent9Raw47AfterRaw112Conditional.p47

noncomputable abbrev roster37 :=
  BB6.Agent9Raw47AfterRaw112Conditional.roster37

theorem raw47_literal_agreement :
    p47 = BB6.Agent50Raw47Depth3Cut.parent :=
  sameTable_sound (by decide)

theorem raw47_cover :
    Cover (WeightedBound 6766859) p47 := by
  rw [raw47_literal_agreement]
  exact BB6.Agent50Raw47Complete.cover_at 6766859 (by decide)

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m :=
  BB6.Agent9Raw47AfterRaw112Conditional.conditional_sound raw47_cover

theorem sound_at (B : Nat) (hFloor : 6766859 ≤ B) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound_integrated m hm with hsmall | hrest
  · exact Or.inl (fun k d hk hd =>
      Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent9Raw47AfterRaw112Conditional.conditional_exact_at_champion_score
    raw47_cover hLeaves

#print axioms raw47_literal_agreement
#print axioms raw47_cover
#print axioms sound_integrated
#print axioms sound_at
#print axioms exact_at_champion_score

end BB6.Agent17Raw47AfterRaw112Integrated

import Raw43Canonical40Bridge
import Raw43Canonical40Conditional

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Source-level successor candidate. Once the complete Raw43 parent closure is
accepted together with the Canonical40 predecessor, this removes Raw43 from
that exact roster and exposes 39 remaining Cover obligations.
-/

namespace BB6.Agent25Raw43Canonical39Successor

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev roster39 :=
  BB6.Agent25Raw43Canonical40Conditional.roster39

theorem count39 : roster39.length = 39 :=
  BB6.Agent25Raw43Canonical40Conditional.count39

theorem raw43_cover :
    Cover (WeightedBound 6766859)
      BB6.Agent25Raw43Canonical40Conditional.p43 :=
  BB6.Agent25Raw43Canonical40Bridge.cover_at_canonical40_floor

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster39, TNFQuotientCompatible e.2 m :=
  BB6.Agent25Raw43Canonical40Conditional.conditional_sound raw43_cover

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster39,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent25Raw43Canonical40Conditional.conditional_exact_at_champion
    raw43_cover hLeaves

#print axioms count39
#print axioms raw43_cover
#print axioms sound_integrated
#print axioms exact_at_champion_score

end BB6.Agent25Raw43Canonical39Successor

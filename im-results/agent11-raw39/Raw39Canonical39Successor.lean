import Raw39Canonical40Bridge
import Raw39Canonical40Conditional

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Ultimate source-level candidate: after original-source acceptance of the complete
Raw39 exact Bound and the Canonical40 conditional successor, this theorem
removes Raw39 from the accepted quotient. Do NOT report unconditional
Canonical39 until this entire source import closure and its axiom profiles
are successfully checked by Lean 4.36.0-rc2.
-/

namespace BB6.Agent11Raw39Canonical39Successor

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev roster39 :=
  BB6.Agent11Raw39Canonical40Conditional.roster39

theorem count39 : roster39.length = 39 :=
  BB6.Agent11Raw39Canonical40Conditional.count39

theorem raw39_cover :
    Cover (WeightedBound 6766859)
      BB6.Agent11Raw39Canonical40Conditional.p39 :=
  BB6.Agent11Raw39Canonical40Bridge.cover_at_champion_threshold

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster39, TNFQuotientCompatible e.2 m :=
  BB6.Agent11Raw39Canonical40Conditional.conditional_sound raw39_cover

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster39,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent11Raw39Canonical40Conditional.conditional_exact_at_champion
    raw39_cover hLeaves

#print axioms count39
#print axioms raw39_cover
#print axioms sound_integrated
#print axioms exact_at_champion_score
end BB6.Agent11Raw39Canonical39Successor

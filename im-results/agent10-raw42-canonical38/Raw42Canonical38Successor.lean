import Raw42AcceptedParent
import Raw42Canonical39Conditional
import Raw42Canonical39FromNamed

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Unconditional cumulative successor on the source-accepted Raw39 Canonical39
lineage.  The complete twelve-child Raw42 parent theorem discharges the only
premise of the previously source-checked conditional 39 -> 38 cut.
-/

namespace BB6.Agent10Raw42Canonical38Successor

open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6ChampionArithmetic

noncomputable abbrev roster38 :=
  BB6.Agent17Raw42Canonical39Conditional.roster38

theorem raw42_cover :
    Cover (WeightedBound 6766859)
      BB6.Agent17Raw42Canonical39Conditional.p42 := by
  rw [← BB6.Agent17Raw42Canonical39FromNamed.literal_eq_p42]
  exact BB6.Agent17Raw42AcceptedParent.cover_global

theorem count38 : roster38.length = 38 :=
  BB6.Agent17Raw42Canonical39Conditional.count38

theorem removed_parent_absent :
    (roster38.filter (fun e =>
      BB6.Agent31FourHoleRoster.sameTable e.2
        BB6.Agent17Raw42Canonical39Conditional.p42)).length = 0 :=
  BB6.Agent17Raw42Canonical39Conditional.removed_parent_absent

theorem sound_integrated :
    ∀ m, compatible BB6.Agent31FourHoleFrontier.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster38,
          TNFQuotientCompatible e.2 m :=
  BB6.Agent17Raw42Canonical39Conditional.conditional_sound raw42_cover

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent17Raw42Canonical39Conditional.conditional_exact_at_champion
    raw42_cover hLeaves

#print axioms raw42_cover
#print axioms count38
#print axioms removed_parent_absent
#print axioms sound_integrated
#print axioms exact_at_champion_score

end BB6.Agent10Raw42Canonical38Successor

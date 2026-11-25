import Canonical73Raw110Composition
import Canonical73Raw113Raw114Raw115Raw117Raw119
import TM63RawUpperInterface

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent38Canonical70

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot
open BB6.Agent47CanonicalRefinement
open BB6ChampionArithmetic
open BB6Coverage.Agent48DirectRoot

/-- The three additional E1 siblings are grafted onto Agent47's
    independently built 73-roster. Together the two routes share only
    raw114 and raw117, so the union has eight distinct parent cuts. -/
noncomputable def roster :=
  graftRoster BB6.Agent25Raw113.p113 []
    (graftRoster BB6.Agent8Raw115.p115 []
      (graftRoster BB6.Agent8Raw119.p119 []
        BB6.Agent47Canonical73Raw110.roster))

/-- Exact cross-route count: 78 canonical entries minus eight distinct
    source-parent cylinders. This is a roster count, not a cover theorem. -/
theorem count : roster.length = 70 := by
  decide

/-- Lift the accepted raw119 parent bound to the raw110 route's 6,766,859
    target, then preserve the full root dichotomy under the graft. -/
theorem after_raw119 :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ graftRoster BB6.Agent8Raw119.p119 []
          BB6.Agent47Canonical73Raw110.roster,
          TNFQuotientCompatible e.2 m := by
  have h119 : ∀ m, compatible BB6.Agent8Raw119.p119 m →
      WeightedBound 6766859 m := by
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent8Raw119.all119 m hm k d hk hd) (by decide)
  exact graftRoster_sound BB6.Agent8Raw119.p119_root
    BB6.Agent47Canonical73Raw110.sound
    (fun m hm => Or.inl (h119 m hm))

/-- Add the raw115 cylinder to the 72-entry intermediate roster. -/
theorem after_raw115 :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ graftRoster BB6.Agent8Raw115.p115 []
          (graftRoster BB6.Agent8Raw119.p119 []
            BB6.Agent47Canonical73Raw110.roster),
          TNFQuotientCompatible e.2 m := by
  have h115 : ∀ m, compatible BB6.Agent8Raw115.p115 m →
      WeightedBound 6766859 m := by
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent8Raw115.all115 m hm k d hk hd) (by decide)
  exact graftRoster_sound BB6.Agent8Raw115.p115_root
    after_raw119
    (fun m hm => Or.inl (h115 m hm))

/-- The exact raw113 parent cover is the final graft; its own generic
    graft theorem accepts any current root roster. -/
theorem sound :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m :=
  BB6.Agent25Raw113.graft113_sound (by decide) after_raw115

/-- The first authentic source increment alone exceeds the raw110 parent
    threshold. This avoids evaluating the enormous full champion score. -/
theorem champion_score_ge_6766859 :
    6766859 ≤ proposedTM63Moves + 7 := by
  rw [← threeSectionScore_root]
  have hfirst :
      proposedIncrementCost 2 7 6 63 ≤
        (sectionResult 7 2 6 63).cost := by
    change proposedIncrementCost 2 7 6 63 ≤
      proposedIncrementCost (2 % 3) 7 6 63 +
        (sectionResult 6 (nextMarker 2) (nextExponent 2 6 63)
          (nextRight 63)).cost
    exact Nat.le_add_right _ _
  have hcost :
      6766859 ≤ proposedIncrementCost 2 7 6 63 := by
    norm_num [proposedIncrementCost, v2]
  have hsection :
      6766859 ≤ (sectionResult 7 2 6 63).cost :=
    Nat.le_trans hcost hfirst
  unfold threeSectionMoves
  omega

/-- Any target at least the raw110 parent bound is exact once all 70
    retained quotient representatives have Covers and an attaining witness
    is supplied. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

/-- The concrete published champion witness supplies attainment at its
    exact score; only the 70 residual Covers remain as premises. -/
theorem exact_from_canonical70_at_champion_score
    (hLeaves : ∀ e ∈ roster,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    champion_score_ge_6766859 hLeaves champion_raw_witness

#print axioms count
#print axioms after_raw119
#print axioms after_raw115
#print axioms sound
#print axioms champion_score_ge_6766859
#print axioms exact_at_target
#print axioms exact_from_canonical70_at_champion_score

end BB6.Agent38Canonical70

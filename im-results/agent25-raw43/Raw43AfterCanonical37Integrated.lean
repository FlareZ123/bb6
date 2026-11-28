import Raw43AfterCanonical37Conditional
import Raw43ParentComplete

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Final Raw43 bridge for the current Raw112-first / Raw47 Canonical37 lineage.
This module is intended to be source-checked only after the complete Raw43
parent artifact is authenticated.  The local parent theorem has weighted bound
11292, which is monotonically lifted to the global 6766859 floor before
discharging the conditional 37 -> 36 cut.
-/

namespace BB6.Agent25Raw43AfterCanonical37Integrated

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p43 : PartialMachine :=
  BB6.Agent25Raw43AfterCanonical37Conditional.p43
noncomputable abbrev roster36 :=
  BB6.Agent25Raw43AfterCanonical37Conditional.roster36

theorem raw43_literal_agreement :
    p43 = BB6.Agent25Raw43Parent.parent :=
  sameTable_sound (by decide)

theorem raw43_cover :
    Cover (WeightedBound 6766859) p43 := by
  apply Cover.leaf
  intro m hm k d hk hd
  have hcompat : compatible BB6.Agent25Raw43Parent.parent m := by
    rw [← raw43_literal_agreement]
    exact hm
  exact Nat.le_trans
    (BB6.Agent38Raw43ParentComplete.cover.sound m hcompat k d hk hd)
    (by decide : 11292 ≤ 6766859)

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m :=
  BB6.Agent25Raw43AfterCanonical37Conditional.conditional_sound raw43_cover

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
  BB6.Agent25Raw43AfterCanonical37Conditional.conditional_exact_at_champion
    raw43_cover hLeaves

#print axioms raw43_literal_agreement
#print axioms raw43_cover
#print axioms sound_integrated
#print axioms sound_at
#print axioms exact_at_champion_score

end BB6.Agent25Raw43AfterCanonical37Integrated

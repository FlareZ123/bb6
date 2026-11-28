import Canonical38Raw47Raw39Conditional
import Raw39Canonical40Bridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Original-source target after the accepted Raw47 Canonical39 successor has been
authenticated and the independently accepted whole Raw39 parent Bound has
been relocated by the Lean kernel into that exact predecessor.

This is NOT a completed BB(6) bound: it removes the *two* accepted parent
Cover obligations from the Canonical40 quotient lineage, leaving 38 explicit
residual Cover obligations. A successful Lean source and axiom audit is needed
before advertising an accepted successor.
-/

namespace BB6.Agent11Canonical38Raw47Raw39

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev roster38 :=
  BB6.Agent45Canonical38Raw47Raw39Conditional.roster38

theorem literal_parent_agreement :
    BB6.Agent45Canonical38Raw47Raw39Conditional.p39 =
      BB6.Agent11Raw39Canonical40Bridge.p :=
  sameTable_sound (by decide)

/-- The independently source-accepted 28,311 Raw39 whole-parent bound
supplies the canonical Raw47-successor's literal Raw39 Cover. -/
theorem raw39_cover_at (B : Nat) (h : 28311 ≤ B) :
    Cover (WeightedBound B)
      BB6.Agent45Canonical38Raw47Raw39Conditional.p39 := by
  rw [literal_parent_agreement]
  exact BB6.Agent11Raw39Canonical40Bridge.weighted_cover B h

theorem count38 : roster38.length = 38 :=
  BB6.Agent45Canonical38Raw47Raw39Conditional.count38

theorem removed_raw39_absent :
    (roster38.filter (fun e =>
      sameTable e.2 BB6.Agent45Canonical38Raw47Raw39Conditional.p39)).length = 0 :=
  BB6.Agent45Canonical38Raw47Raw39Conditional.removed_parent_absent

/-- The accepted Raw47→Canonical39 theorem together with the original
whole-parent Raw39 theorem leaves **exactly 38** other quotient obligations
at any score B ≥ 6,766,859 and B ≥ 28,311. -/
theorem sound38_at (B : Nat) (hFloor : 6766859 ≤ B)
    (hParent : 28311 ≤ B) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m :=
  BB6.Agent45Canonical38Raw47Raw39Conditional.conditional_sound_at
    B hFloor (raw39_cover_at B hParent)

/-- Raw47 and Raw39 are already discharged on the *same authenticated*
lineage. Only the 38 retained literal Covers remain as hypotheses. -/
theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent45Canonical38Raw47Raw39Conditional.conditional_exact_at_champion
    (raw39_cover_at (proposedTM63Moves + 7)
      (Nat.le_trans (by decide : 28311 ≤ 6766859)
        BB6.Agent38ChampionThreshold.champion_score_ge_6766859))
    hLeaves

#print axioms literal_parent_agreement
#print axioms raw39_cover_at
#print axioms count38
#print axioms removed_raw39_absent
#print axioms sound38_at
#print axioms exact_at_champion_score

end BB6.Agent11Canonical38Raw47Raw39

import Canonical67E1ParentGraft
import Canonical68Integrated
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Canonical67Integrated

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent6Canonical68E1ParentGraft
open BB6.Agent31Canonical68Integrated
open BB6.Agent47Canonical67E1ParentGraft
open BB6.Agent47CanonicalRefinement
open BB6.Agent47Raw112

/-- The integrated consumer must graft Raw112 onto the exact roster used by
    Canonical68Integrated.sound68_integrated.  This is deliberately distinct
    from the sequential E1-interface roster in Canonical67E1ParentGraft.lean. -/
noncomputable def roster67Integrated : List Entry :=
  graftRoster BB6.Agent47Canonical67E1ParentGraft.p112 []
    BB6.Agent31Canonical68Integrated.roster68

/-- Raw112 occurs exactly once in the integrated Canonical68 roster. -/
theorem p112_parent_count_integrated :
    (BB6.Agent31Canonical68Integrated.roster68.filter
      (fun e => sameTable e.2 BB6.Agent47Canonical67E1ParentGraft.p112)).length = 1 := by
  decide

/-- The integrated base roster loses exactly the Raw112 parent. -/
theorem count67_integrated : roster67Integrated.length = 67 := by
  decide

/-- The Raw112 parent in the graft is definitionally the table certified by
    the independently source-audited Raw112 closed-cover development. -/
theorem p112_eq :
    BB6.Agent47Canonical67E1ParentGraft.p112 = BB6.Agent47Raw112.parent := by
  rfl

/-- Source-accepted Raw112 cover, lifted to the canonical champion bound. -/
theorem raw112_cover :
    Cover (WeightedBound 100000) BB6.Agent47Canonical67E1ParentGraft.p112 := by
  rw [p112_eq]
  exact BB6.Agent47Raw112.parent_cover

/-- All nine parent cylinders are consumed against one coherent base roster:
    the eight integrated Canonical68 Covers plus the Raw112 closed Cover. -/
theorem sound67_integrated :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster67Integrated, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound
    (p := BB6.Agent47Canonical67E1ParentGraft.p112)
    (replacement := [])
    (roster := BB6.Agent31Canonical68Integrated.roster68)
    BB6.Agent47Canonical67E1ParentGraft.p112_root
    BB6.Agent31Canonical68Integrated.sound68_integrated
  intro m hm
  exact Or.inl (
    BB6.Agent6Canonical68E1ParentGraft.lift_parent_cover
      (by decide) raw112_cover m hm
  )

/-- Conditional exactness at the champion score: 67 quotient Covers and an
    attaining blank-start witness remain explicit. -/
theorem exact_at_target67 (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster67Integrated, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound67_integrated hLeaves champ

#print axioms p112_parent_count_integrated
#print axioms count67_integrated
#print axioms p112_eq
#print axioms raw112_cover
#print axioms sound67_integrated
#print axioms exact_at_target67

end BB6.Agent47Canonical67Integrated

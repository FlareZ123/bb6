import Canonical67E1ParentGraft
import Raw118CanonicalCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Canonical66E1ParentGraft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent6Canonical68E1ParentGraft
open BB6.Agent16Raw118CanonicalCut
open BB6.Agent47Canonical67E1ParentGraft
open BB6.Agent47CanonicalRefinement

/-- First remove Raw118 from the 68-parent roster. -/
noncomputable def roster67_118 := graftRoster p118 [] roster68

/-- Then remove Raw112 from that 67-parent roster. -/
noncomputable def roster66 := graftRoster p112 [] roster67_118

/-- Raw112 remains exactly once after the distinct Raw118 cut. -/
theorem p112_parent_count_after_p118 :
    (roster67_118.filter (fun e => sameTable e.2 p112)).length = 1 := by
  decide

/-- The two disjoint E1 parent cuts leave 66 exact quotient obligations. -/
theorem count66 : roster66.length = 66 := by
  decide

/-- Conditional 66-roster soundness from the accepted 68-roster interface,
    together with the two local parent Covers. -/
theorem sound66 (B : Nat) (hB : 6766859 ≤ B)
    (h68 : ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster68, TNFQuotientCompatible e.2 m)
    (h118 : Cover (WeightedBound 756496) p118)
    (h112 : Cover (WeightedBound 100000) p112) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster66, TNFQuotientCompatible e.2 m := by
  have h68B : ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster68, TNFQuotientCompatible e.2 m := by
    intro m hm
    rcases h68 m hm with hbound | hrest
    · exact Or.inl (fun k d hk hd => Nat.le_trans (hbound k d hk hd) hB)
    · exact Or.inr hrest
  have h67 := sound_cut (by omega) h68B h118
  apply graftRoster_sound (p := p112) (replacement := []) (roster := roster67_118)
    p112_root h67
  intro m hm
  exact Or.inl (fun k d hk hd =>
    Nat.le_trans (lift_parent_cover (by decide) h112 m hm k d hk hd) hB)

/-- Conditional exactness after both parent cylinders are consumed; the
    remaining 66 quotient obligations stay explicit. -/
theorem exact_at_target66 (B : Nat) (hB : 6766859 ≤ B)
    (h68 : ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster68, TNFQuotientCompatible e.2 m)
    (h118 : Cover (WeightedBound 756496) p118)
    (h112 : Cover (WeightedBound 100000) p112)
    (hLeaves : ∀ e ∈ roster66, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB
    (sound66 B hB h68 h118 h112) hLeaves champ

#print axioms p112_parent_count_after_p118
#print axioms count66
#print axioms sound66
#print axioms exact_at_target66

end BB6.Agent47Canonical66E1ParentGraft

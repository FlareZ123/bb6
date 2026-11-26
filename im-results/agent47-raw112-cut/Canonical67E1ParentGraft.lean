import Canonical68E1ParentGraft
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Canonical67E1ParentGraft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent6Canonical68E1ParentGraft

/-- The ninth E1 sibling: Raw112's fixed 1LC transition. -/
abbrev p112 : PartialMachine := refine e1Base (4,true) (some ⟨true,false,2⟩)

/-- The Raw112 parent has the same standard first-one root transition. -/
theorem p112_root : p112 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Raw112 occurs exactly once among the 68 retained quotient representatives. -/
theorem p112_parent_count :
    (roster68.filter (fun e => sameTable e.2 p112)).length = 1 := by
  decide

/-- Removing Raw112 from the accepted 68 roster leaves 67 exact obligations. -/
noncomputable def roster67 := graftRoster p112 [] roster68

theorem count67 : roster67.length = 67 := by
  decide

/-- Conditional 67-roster soundness.  The only new premise beyond the eight
    already consumed by Canonical68 is the Raw112 parent Cover. -/
theorem sound67
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60)
    (h110 : Cover (WeightedBound 6766859) p110)
    (h111 : Cover (WeightedBound 7014) p111)
    (h117 : Cover (WeightedBound 1291) p117)
    (h121 : Cover (WeightedBound 4063) p121)
    (h125 : Cover (WeightedBound 1290) p125)
    (h112 : Cover (WeightedBound 100000) p112) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster67, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p112) (replacement := []) (roster := roster68)
    p112_root (sound68 h109 h123 h60 h110 h111 h117 h121 h125)
  intro m hm
  exact Or.inl (lift_parent_cover (by decide) h112 m hm)

/-- Conditional exactness after the Raw112 parent is consumed as well.
    The remaining 67 quotient representatives are still explicit. -/
theorem exact_at_target67 (B : Nat) (hB : 6766859 ≤ B)
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60)
    (h110 : Cover (WeightedBound 6766859) p110)
    (h111 : Cover (WeightedBound 7014) p111)
    (h117 : Cover (WeightedBound 1291) p117)
    (h121 : Cover (WeightedBound 4063) p121)
    (h125 : Cover (WeightedBound 1290) p125)
    (h112 : Cover (WeightedBound 100000) p112)
    (hLeaves : ∀ e ∈ roster67, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB
    (sound67 h109 h123 h60 h110 h111 h117 h121 h125 h112)
    hLeaves champ

#print axioms p112_root
#print axioms p112_parent_count
#print axioms count67
#print axioms sound67
#print axioms exact_at_target67

end BB6.Agent47Canonical67E1ParentGraft

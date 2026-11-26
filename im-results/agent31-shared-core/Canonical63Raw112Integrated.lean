import Canonical64Raw120Integrated
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical63Raw112

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalFrontier
open BB6.Agent3Canonical64Raw120
open BB6.Agent47Raw112

/-- The Raw112 six-hole parent, already certified at weighted bound 100000. -/
abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent

/-- Raw112 has the standard first-one blank-start transition. -/
theorem p112_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Raw112 remains exactly once in the accepted 64-entry quotient roster. -/
theorem p112_count :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p112)).length = 1 := by
  decide

/-- Remove the accepted Raw112 parent from the integrated 64-entry roster. -/
noncomputable def roster63 :=
  removeParents [p112] BB6.Agent3Canonical64Raw120.roster64

theorem count63 : roster63.length = 63 := by
  decide

/-- The source-accepted Raw112 parent Cover. -/
theorem raw112_cover : Cover (WeightedBound 100000) p112 :=
  BB6.Agent47Raw112.parent_cover

/-- Lift any accepted parent Cover to the common Raw110 binding floor. -/
theorem lift_parent_cover {C : Nat} {p : PartialMachine}
    (hC : C ≤ 6766859) (h : Cover (WeightedBound C) p) :
    Cover (WeightedBound 6766859) p := by
  intro m hm k d hk hd
  exact Nat.le_trans (h.sound m hm k d hk hd) hC

/-- Integrated Raw112 composition: the accepted 64-roster theorem plus the
    Raw112 parent Cover leaves exactly 63 quotient representatives. -/
theorem sound63_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster63, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound
    (parents := [p112])
    (roster := BB6.Agent3Canonical64Raw120.roster64)
    BB6.Agent3Canonical64Raw120.sound64_integrated
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact p112_root
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact lift_parent_cover (by decide) raw112_cover

/-- Conditional exactness after Raw112 is consumed: 63 quotient Covers at
    the target bound and an attaining blank-start witness remain explicit. -/
theorem exact_at_target63 (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster63, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound63_integrated hLeaves champ

#print axioms p112_root
#print axioms p112_count
#print axioms count63
#print axioms raw112_cover
#print axioms sound63_integrated
#print axioms exact_at_target63

end BB6.Agent31Canonical63Raw112

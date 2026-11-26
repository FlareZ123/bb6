import Canonical67E1ParentGraft
import Canonical68Integrated
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Canonical67Integrated

open BB6Coverage
open BB6.Agent6Canonical68E1ParentGraft
open BB6.Agent31Canonical68Integrated
open BB6.Agent47Canonical67E1ParentGraft
open BB6.Agent47Raw112

/-- The Raw112 parent in the 68-to-67 graft is definitionally the
    parent certified by the Raw112 closed-cover development. -/
theorem p112_eq : p112 = BB6.Agent47Raw112.parent := by
  rfl

/-- Source-accepted Raw112 cover, lifted to the canonical champion bound. -/
theorem raw112_cover : Cover (WeightedBound 100000) p112 := by
  rw [p112_eq]
  exact BB6.Agent47Raw112.parent_cover

/-- All nine parent cylinders are now consumed: the eight existing
    Canonical68 covers plus the Raw112 closed cover. -/
theorem sound67_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster67, TNFQuotientCompatible e.2 m := by
  exact sound67 cover109.sound cover123 cover60 cover110 cover111
    cover117 cover121 cover125 raw112_cover

/-- The exact BB(6) target now has 67, rather than 68, quotient
    obligations, with the champion lower bound unchanged. -/
theorem exact_at_target67 (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster67, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound67_integrated hLeaves champ

#print axioms p112_eq
#print axioms raw112_cover
#print axioms sound67_integrated
#print axioms exact_at_target67

end BB6.Agent47Canonical67Integrated

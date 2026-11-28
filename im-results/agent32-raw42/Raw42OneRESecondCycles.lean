import Raw42Cut

/-!
Four original-source, independent cyclic/side-cyclic nonhalting cylinders
under Raw42 B1 = 1RE.  Only B1 and E0 are newly assigned, so each theorem
holds for all choices of the five remaining undefined transitions.

The witnesses are finite zipper-period certificates. The boolean verifier
`zipCycle` and its mathematical soundness proof are imported from
`ZipAuditCore`; no independent simulation assertion is trusted.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42OneRESecondCycles

open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit

abbrev base : PartialMachine :=
  BB6.Agent32Raw42.child ⟨true,true,4⟩

namespace ZeroLB
abbrev p : PartialMachine := refine base (4,false) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 2 false 1 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 6 2 false 1 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLB

namespace ZeroLD
abbrev p : PartialMachine := refine base (4,false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 36 22 false 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 36 22 false 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLD

namespace ZeroRD
abbrev p : PartialMachine := refine base (4,false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 6 11 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 6 11 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRD

namespace OneRD
abbrev p : PartialMachine := refine base (4,false) (some ⟨true,true,3⟩)
theorem check : zipCycle p 8 7 true 1 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 8 7 true 1 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRD

end BB6.Agent32Raw42OneRESecondCycles

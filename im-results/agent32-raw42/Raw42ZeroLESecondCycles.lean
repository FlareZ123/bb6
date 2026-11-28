import Raw42Cut

/-!
Direct original-source nonhalting certificates for 0LE first child
of Raw42, then its E0 transition. Every claimed cylinder has exactly five
remaining free transitions. These are derived from finite side-period
witnesses and proved by `zipCycle_sound`, not simulation alone.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42ZeroLESecondCycles
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit

abbrev base : PartialMachine :=
  BB6.Agent32Raw42.child ⟨false,false,4⟩

namespace ZeroLA
abbrev p : PartialMachine := refine base (4,false) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 8 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 0 8 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLA

namespace ZeroLC
abbrev p : PartialMachine := refine base (4,false) (some ⟨false,false,2⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 9 1 false (-1) (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLC

namespace ZeroLD
abbrev p : PartialMachine := refine base (4,false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 8 1 false (-2) (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLD

namespace ZeroLE
abbrev p : PartialMachine := refine base (4,false) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 1 false (-1) = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 7 1 false (-1) (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLE

namespace ZeroRC
abbrev p : PartialMachine := refine base (4,false) (some ⟨false,true,2⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 9 1 false 1 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRC

namespace ZeroRD
abbrev p : PartialMachine := refine base (4,false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 8 1 false 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 8 1 false 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRD

namespace OneLD
abbrev p : PartialMachine := refine base (4,false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 8 1 false (-2) (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLD

namespace OneLE
abbrev p : PartialMachine := refine base (4,false) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 1 false (-1) = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 7 1 false (-1) (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLE

namespace OneRD
abbrev p : PartialMachine := refine base (4,false) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 12 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRD

end BB6.Agent32Raw42ZeroLESecondCycles

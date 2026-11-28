import Raw42Cut
/-!
Exact original-source finite zipper certificates on the third unknown slot
of the Raw42 branch OneREZeroRB. In each theorem, the first and second unknown
moves are fixed and the third is refined, leaving four transition slots free.
These are bounded true/false zipper checks plus the proved zipCycle_sound lemma.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42OneREZeroRBThirdCycles
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
abbrev base : PartialMachine := BB6.Agent32Raw42.child
  ⟨true,true,4⟩
abbrev second : PartialMachine :=
  refine base (4,false) (some ⟨false,true,1⟩)

namespace ZeroLB
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 22 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLB

namespace ZeroLD
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 10 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 10 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLD

namespace ZeroLE
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 22 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLE

namespace ZeroRA
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 0 10 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRA

namespace ZeroRB
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 20 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRB

namespace ZeroRC
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 23 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRC

namespace ZeroRD
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 18 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 18 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRD

namespace ZeroRE
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 21 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 21 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRE

namespace OneLB
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 8 2 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 8 2 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLB

namespace OneLD
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 13 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLD

namespace OneLE
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 4 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 7 4 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLE

namespace OneRA
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 0 10 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRA

namespace OneRB
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 9 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 9 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRB

namespace OneRC
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 2 8 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 2 8 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRC

namespace OneRD
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 26 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 26 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRD

namespace OneRE
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 1 21 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 21 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRE

end BB6.Agent32Raw42OneREZeroRBThirdCycles

import Raw42Cut
/-!
Exact original-source finite zipper certificates on the third unknown slot
of the Raw42 branch ZeroLEZeroLB. In each theorem, the first and second unknown
moves are fixed and the third is refined, leaving four transition slots free.
These are bounded true/false zipper checks plus the proved zipCycle_sound lemma.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42ZeroLEZeroLBThirdCycles
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
abbrev base : PartialMachine := BB6.Agent32Raw42.child
  ⟨false,false,4⟩
abbrev second : PartialMachine :=
  refine base (4,false) (some ⟨false,false,1⟩)

namespace ZeroLA
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 26 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 0 26 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLA

namespace ZeroLB
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 8 18 false 1 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 8 18 false 1 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLB

namespace ZeroLC
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 27 1 false -3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 27 1 false -3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLC

namespace ZeroLD
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 26 1 false -4 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 26 1 false -4 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLD

namespace ZeroLE
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 19 false 1 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 7 19 false 1 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLE

namespace ZeroRB
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 32 13 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 32 13 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRB

namespace ZeroRC
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 27 1 false -1 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 27 1 false -1 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRC

namespace ZeroRD
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 26 1 false -2 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 26 1 false -2 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRD

namespace OneLA
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 24 3 false -2 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 24 3 false -2 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLA

namespace OneLC
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 8 20 false 1 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 8 20 false 1 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLC

namespace OneLD
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 26 1 false -4 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 26 1 false -4 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLD

namespace OneLE
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 1 29 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 29 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLE

namespace OneRB
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 32 13 true 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 32 13 true 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRB

namespace OneRD
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 30 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 30 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRD

namespace OneRE
abbrev p : PartialMachine :=
  refine second (4,true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 6 21 false 1 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 6 21 false 1 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRE

end BB6.Agent32Raw42ZeroLEZeroLBThirdCycles

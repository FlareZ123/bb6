import Raw42Cut
/-!
Original-source finite side-cycle certification under Raw42 B1 = 1LB,
then C1 assigned. Exactly five transitions remain free in each cylinder.
No source certificates are admitted by external simulation.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42OneLBSecondCycles
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
abbrev base : PartialMachine :=
  BB6.Agent32Raw42.child ⟨true,false,1⟩

namespace ZeroLB
abbrev p : PartialMachine := refine base (2,true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 6 3 false 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLB

namespace ZeroLC
abbrev p : PartialMachine := refine base (2,true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 11 1 false (-1) (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroLC

namespace ZeroRB
abbrev p : PartialMachine := refine base (2,true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 6 36 true (-1) = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 6 36 true (-1) (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRB

namespace ZeroRC
abbrev p : PartialMachine := refine base (2,true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 13 true (-1) (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end ZeroRC

namespace OneLB
abbrev p : PartialMachine := refine base (2,true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 6 3 false 0 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLB

namespace OneLC
abbrev p : PartialMachine := refine base (2,true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 14 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLC

namespace OneLD
abbrev p : PartialMachine := refine base (2,true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 1 12 false 3 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneLD

namespace OneRB
abbrev p : PartialMachine := refine base (2,true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 13 5 false 1 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 13 5 false 1 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRB

namespace OneRD
abbrev p : PartialMachine := refine base (2,true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 4 5 false 2 = true := by decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  zipCycle_sound p 4 5 false 2 (by decide) check m hm
theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover
end OneRD

end BB6.Agent32Raw42OneLBSecondCycles

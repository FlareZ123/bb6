import FastPhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
open BB6Coverage.Agent13PackedZipper BB6.Agent5FastPhaseTree

namespace BB6.Agent44Extra59Hole00
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
def z0 : P := startP
def z2484 : P := ⟨4,0,17538492373449⟩
theorem span0_2484 : runP p 2484 z0 = some z2484 := by decide +kernel
theorem safe : ∀ m, compatible p m → WeightedBound 2490 m :=
  lastPacked 2490 p 2484 (4,false) z2484 span0_2484 (by decide) (by decide) (by decide) (by decide) (by decide)
theorem cover : Cover (WeightedBound 2490) p := .leaf _ safe
#print axioms cover
end BB6.Agent44Extra59Hole00

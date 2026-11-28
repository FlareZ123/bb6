import FastPhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
open BB6Coverage.Agent13PackedZipper BB6.Agent5FastPhaseTree

namespace BB6.Agent44Extra48Hole00
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
def z0 : P := startP
def z4096 : P := ⟨1,6588122883467697006,174936648⟩
def z4869 : P := ⟨4,14147886163261488856030736119,20⟩
theorem span0_4096 : runP p 4096 z0 = some z4096 := by decide +kernel
theorem span4096_4869 : runP p 773 z4096 = some z4869 := by decide +kernel
theorem span0_4869 : runP p 4869 z0 = some z4869 := joinP span0_4096 span4096_4869
theorem safe : ∀ m, compatible p m → WeightedBound 4875 m :=
  lastPacked 4875 p 4869 (4,true) z4869 span0_4869 (by decide) (by decide) (by decide) (by decide) (by decide)
theorem cover : Cover (WeightedBound 4875) p := .leaf _ safe
#print axioms cover
end BB6.Agent44Extra48Hole00

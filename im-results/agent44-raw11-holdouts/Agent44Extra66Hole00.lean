import FastPhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
open BB6Coverage.Agent13PackedZipper BB6.Agent5FastPhaseTree

namespace BB6.Agent44Extra66Hole00
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨false,false,5⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
def z0 : P := startP
def z2430 : P := ⟨5,3,4282279874254003054⟩
theorem span0_2430 : runP p 2430 z0 = some z2430 := by decide +kernel
theorem safe : ∀ m, compatible p m → WeightedBound 2436 m :=
  lastPacked 2436 p 2430 (5,true) z2430 span0_2430 (by decide) (by decide) (by decide) (by decide) (by decide)
theorem cover : Cover (WeightedBound 2436) p := .leaf _ safe
#print axioms cover
end BB6.Agent44Extra66Hole00

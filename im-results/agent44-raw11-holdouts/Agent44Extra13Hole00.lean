import FastPhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
open BB6Coverage.Agent13PackedZipper BB6.Agent5FastPhaseTree

namespace BB6.Agent44Extra13Hole00
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none
def z0 : P := startP
def z4096 : P := ⟨0,1073891620,613566757⟩
def z8192 : P := ⟨1,36174560846189128,153391689⟩
def z12288 : P := ⟨1,10958588735390645264468261,149796⟩
def z15937 : P := ⟨5,0,5934053552611231575463424376251732⟩
theorem span0_4096 : runP p 4096 z0 = some z4096 := by decide +kernel
theorem span4096_8192 : runP p 4096 z4096 = some z8192 := by decide +kernel
theorem span8192_12288 : runP p 4096 z8192 = some z12288 := by decide +kernel
theorem span12288_15937 : runP p 3649 z12288 = some z15937 := by decide +kernel
theorem span0_8192 : runP p 8192 z0 = some z8192 := joinP span0_4096 span4096_8192
theorem span8192_15937 : runP p 7745 z8192 = some z15937 := joinP span8192_12288 span12288_15937
theorem span0_15937 : runP p 15937 z0 = some z15937 := joinP span0_8192 span8192_15937
theorem safe : ∀ m, compatible p m → WeightedBound 15943 m :=
  lastPacked 15943 p 15937 (5,false) z15937 span0_15937 (by decide) (by decide) (by decide) (by decide) (by decide)
theorem cover : Cover (WeightedBound 15943) p := .leaf _ safe
#print axioms cover
end BB6.Agent44Extra13Hole00

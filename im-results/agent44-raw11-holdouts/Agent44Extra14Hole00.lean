import FastPhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
open BB6Coverage.Agent13PackedZipper BB6.Agent5FastPhaseTree

namespace BB6.Agent44Extra14Hole00
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none
def z0 : P := startP
def z4096 : P := ⟨2,35184372088831,4294965930⟩
def z8192 : P := ⟨4,73786976294838206463,2199023254186⟩
def z12288 : P := ⟨3,281474976710655,19342813113834066795298805⟩
def z16384 : P := ⟨3,0,356811923121105470440199997658048489917338965⟩
def z20480 : P := ⟨5,30,19029969236079465080777146259326601818436621653⟩
def z20790 : P := ⟨4,2923003274661805836407369665432566039311865085950,0⟩
theorem span0_4096 : runP p 4096 z0 = some z4096 := by decide +kernel
theorem span4096_8192 : runP p 4096 z4096 = some z8192 := by decide +kernel
theorem span8192_12288 : runP p 4096 z8192 = some z12288 := by decide +kernel
theorem span12288_16384 : runP p 4096 z12288 = some z16384 := by decide +kernel
theorem span16384_20480 : runP p 4096 z16384 = some z20480 := by decide +kernel
theorem span20480_20790 : runP p 310 z20480 = some z20790 := by decide +kernel
theorem span0_8192 : runP p 8192 z0 = some z8192 := joinP span0_4096 span4096_8192
theorem span8192_16384 : runP p 8192 z8192 = some z16384 := joinP span8192_12288 span12288_16384
theorem span16384_20790 : runP p 4406 z16384 = some z20790 := joinP span16384_20480 span20480_20790
theorem span0_16384 : runP p 16384 z0 = some z16384 := joinP span0_8192 span8192_16384
theorem span0_20790 : runP p 20790 z0 = some z20790 := joinP span0_16384 span16384_20790
theorem safe : ∀ m, compatible p m → WeightedBound 20796 m :=
  lastPacked 20796 p 20790 (4,false) z20790 span0_20790 (by decide) (by decide) (by decide) (by decide) (by decide)
theorem cover : Cover (WeightedBound 20796) p := .leaf _ safe
#print axioms cover
end BB6.Agent44Extra14Hole00

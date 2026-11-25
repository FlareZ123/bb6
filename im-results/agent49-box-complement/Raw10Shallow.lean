import Raw10Orbit
import SideWitnessCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Raw10Shallow
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6.Agent47SevenSideWitnesses
open BB6.Agent49BoxBridge BB6.Agent49Raw10Orbit
open BB6.Agent13CrossRouteHeldLeaf109

structure HaltWitness where
  rows : List Nat
  steps : Nat
  slot : Slot

def HaltWitness.parent (w : HaltWitness) : PartialMachine :=
  unpackTable (decodeRows w.rows)

def HaltWitness.closed (w : HaltWitness) : PartialMachine :=
  refine w.parent w.slot none

def HaltWitness.check (w : HaltWitness) : Bool :=
  decide (w.parent initialSlot = some (some ⟨true,true,1⟩)) &&
  decide (w.parent w.slot = none) &&
  decide ((knownRun w.parent w.steps).map readSlot = some w.slot) &&
  weightOK w.parent w.slot w.steps 7014

theorem HaltWitness.sound (w : HaltWitness) (h : w.check = true) :
    ∀ m, compatible w.closed m → WeightedBound 7014 m := by
  simp only [HaltWitness.check, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hf,hh⟩,hread⟩,hw⟩
  intro m hm
  cases hr : knownRun w.parent w.steps with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = w.slot := by simpa [hr] using hread
    exact first_hole_weighted_halt 7014 w.parent w.steps c hf hr
      (by simpa only [hs] using hh)
      (by simpa only [hs] using weightOK_sound w.parent w.slot w.steps 7014 hw)
      m (by simpa only [hs,HaltWitness.closed] using hm)

def sideChunk0 : List SideWitness := [
  ⟨[8,0,11,0,0,1,0,0,0,0,0,0],0,3,false,(1)⟩,
  ⟨[8,1,11,0,0,2,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,2,11,0,0,2,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,4,11,0,0,2,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,8,11,0,0,2,0,0,0,0,0,0],1,3,true,(0)⟩,
  ⟨[8,0,11,9,0,3,0,0,0,0,0,0],2,3,false,(0)⟩,
  ⟨[8,0,11,11,0,3,0,0,0,0,0,0],2,3,false,(0)⟩,
  ⟨[8,1,11,0,0,4,0,0,0,0,0,0],0,5,false,(1)⟩,
  ⟨[8,2,11,0,0,4,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,4,11,0,0,4,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,8,11,0,0,4,0,0,0,0,0,0],1,3,true,(0)⟩,
  ⟨[8,9,11,0,0,4,0,0,0,0,0,0],0,5,true,(0)⟩
]
theorem sideChunk0_checked : sideChunk0.all SideWitness.check = true := by decide

def sideChunk1 : List SideWitness := [
  ⟨[8,11,11,0,0,4,0,0,0,0,0,0],2,2,true,(0)⟩,
  ⟨[8,0,11,0,1,5,0,0,0,0,0,0],0,5,false,(1)⟩,
  ⟨[8,0,11,0,5,5,0,0,0,0,0,0],3,2,false,(-1)⟩,
  ⟨[8,0,11,0,7,5,0,0,0,0,0,0],3,2,false,(-1)⟩,
  ⟨[8,0,11,0,9,5,0,0,0,0,0,0],4,1,false,(-2)⟩,
  ⟨[8,0,11,0,10,5,0,0,0,0,0,0],2,3,false,(0)⟩,
  ⟨[8,0,11,0,11,5,0,0,0,0,0,0],4,1,false,(-2)⟩,
  ⟨[8,0,11,1,0,6,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,0,11,2,0,6,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,0,11,4,0,6,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,0,11,8,0,6,0,0,0,0,0,0],1,3,true,(0)⟩,
  ⟨[8,0,11,0,1,7,0,0,0,0,0,0],0,5,false,(1)⟩
]
theorem sideChunk1_checked : sideChunk1.all SideWitness.check = true := by decide

def sideChunk2 : List SideWitness := [
  ⟨[8,0,11,0,5,7,0,0,0,0,0,0],3,2,false,(-1)⟩,
  ⟨[8,0,11,0,7,7,0,0,0,0,0,0],3,2,false,(-1)⟩,
  ⟨[8,0,11,0,9,7,0,0,0,0,0,0],4,1,false,(-2)⟩,
  ⟨[8,0,11,0,10,7,0,0,0,0,0,0],2,3,false,(0)⟩,
  ⟨[8,0,11,0,11,7,0,0,0,0,0,0],4,1,false,(-2)⟩,
  ⟨[8,0,11,2,0,8,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,0,11,4,0,8,0,0,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,0,11,8,0,8,0,0,0,0,0,0],1,3,true,(0)⟩,
  ⟨[8,0,11,9,0,8,0,0,0,0,0,0],1,4,true,(0)⟩,
  ⟨[8,0,11,11,0,8,0,0,0,0,0,0],2,2,true,(0)⟩,
  ⟨[8,0,11,0,1,9,0,0,0,0,0,0],0,4,false,(1)⟩,
  ⟨[8,0,11,0,5,9,0,0,0,0,0,0],3,2,false,(-1)⟩
]
theorem sideChunk2_checked : sideChunk2.all SideWitness.check = true := by decide

def sideChunk3 : List SideWitness := [
  ⟨[8,0,11,0,7,9,0,0,0,0,0,0],3,2,false,(-1)⟩,
  ⟨[8,0,11,0,8,9,0,0,0,0,0,0],1,3,false,(1)⟩,
  ⟨[8,0,11,0,9,9,0,0,0,0,0,0],3,1,false,(-1)⟩,
  ⟨[8,0,11,0,10,9,0,0,0,0,0,0],6,1,true,(0)⟩,
  ⟨[8,0,11,0,11,9,0,0,0,0,0,0],3,1,false,(-1)⟩,
  ⟨[8,0,11,0,12,9,0,0,0,0,0,0],8,1,true,(-2)⟩,
  ⟨[8,0,11,0,1,10,0,0,0,0,0,0],0,5,true,(0)⟩,
  ⟨[8,0,11,0,2,10,0,0,0,0,0,0],0,5,true,(0)⟩,
  ⟨[8,0,11,0,4,10,0,0,0,0,0,0],0,5,true,(0)⟩,
  ⟨[8,0,11,0,5,10,0,0,0,0,0,0],4,2,false,(2)⟩,
  ⟨[8,0,11,0,7,10,0,0,0,0,0,0],4,2,false,(2)⟩,
  ⟨[8,0,11,0,8,10,0,0,0,0,0,0],1,4,true,(0)⟩
]
theorem sideChunk3_checked : sideChunk3.all SideWitness.check = true := by decide

def sideChunk4 : List SideWitness := [
  ⟨[8,0,11,0,9,10,0,0,0,0,0,0],4,1,false,(2)⟩,
  ⟨[8,0,11,0,10,10,0,0,0,0,0,0],4,1,true,(2)⟩,
  ⟨[8,0,11,0,11,10,0,0,0,0,0,0],4,1,false,(2)⟩,
  ⟨[8,0,11,0,12,10,0,0,0,0,0,0],4,1,true,(2)⟩,
  ⟨[8,0,11,0,1,11,0,0,0,0,0,0],0,4,false,(1)⟩,
  ⟨[8,0,11,0,5,11,0,0,0,0,0,0],3,2,false,(-1)⟩,
  ⟨[8,0,11,0,7,11,0,0,0,0,0,0],3,2,false,(-1)⟩,
  ⟨[8,0,11,0,9,11,0,0,0,0,0,0],3,1,false,(-1)⟩,
  ⟨[8,0,11,0,10,11,0,0,0,0,0,0],2,2,true,(-1)⟩,
  ⟨[8,0,11,0,11,11,0,0,0,0,0,0],3,1,false,(-1)⟩,
  ⟨[8,0,11,0,12,11,0,0,0,0,0,0],2,3,false,(0)⟩,
  ⟨[8,0,11,0,2,12,0,0,0,0,0,0],0,5,true,(0)⟩
]
theorem sideChunk4_checked : sideChunk4.all SideWitness.check = true := by decide

def sideChunk5 : List SideWitness := [
  ⟨[8,0,11,0,4,12,0,0,0,0,0,0],0,5,true,(0)⟩,
  ⟨[8,0,11,0,8,12,0,0,0,0,0,0],1,4,true,(0)⟩,
  ⟨[8,0,11,0,9,12,0,0,0,0,0,0],3,2,true,(1)⟩,
  ⟨[8,0,11,0,10,12,0,0,0,0,0,0],4,1,true,(2)⟩,
  ⟨[8,0,11,0,11,12,0,0,0,0,0,0],2,3,true,(0)⟩,
  ⟨[8,0,11,0,12,12,0,0,0,0,0,0],4,1,true,(2)⟩,
  ⟨[8,0,11,0,0,13,1,0,0,0,0,0],0,4,false,(1)⟩,
  ⟨[8,0,11,0,0,13,8,0,0,0,0,0],1,3,false,(1)⟩,
  ⟨[8,0,11,0,0,13,13,0,0,0,0,0],3,1,false,(-1)⟩,
  ⟨[8,0,11,0,0,13,15,0,0,0,0,0],3,1,false,(-1)⟩,
  ⟨[8,0,11,0,0,14,0,1,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,0,11,0,0,14,0,2,0,0,0,0],0,4,true,(0)⟩
]
theorem sideChunk5_checked : sideChunk5.all SideWitness.check = true := by decide

def sideChunk6 : List SideWitness := [
  ⟨[8,0,11,0,0,14,0,4,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,0,11,0,0,14,0,8,0,0,0,0],1,3,true,(0)⟩,
  ⟨[8,0,11,0,0,15,1,0,0,0,0,0],0,4,false,(1)⟩,
  ⟨[8,0,11,0,0,15,10,0,0,0,0,0],2,2,true,(-1)⟩,
  ⟨[8,0,11,0,0,15,13,0,0,0,0,0],3,1,false,(-1)⟩,
  ⟨[8,0,11,0,0,15,15,0,0,0,0,0],3,1,false,(-1)⟩,
  ⟨[8,0,11,0,0,16,0,2,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,0,11,0,0,16,0,4,0,0,0,0],0,4,true,(0)⟩,
  ⟨[8,0,11,0,0,16,0,8,0,0,0,0],1,3,true,(0)⟩,
  ⟨[8,0,11,0,0,16,0,11,0,0,0,0],2,2,true,(0)⟩
]
theorem sideChunk6_checked : sideChunk6.all SideWitness.check = true := by decide

def sideData : List SideWitness := sideChunk0 ++ sideChunk1 ++ sideChunk2 ++ sideChunk3 ++ sideChunk4 ++ sideChunk5 ++ sideChunk6
theorem sideData_checked : sideData.all SideWitness.check = true := by
  simp only [sideData,List.all_append,sideChunk0_checked,sideChunk1_checked,sideChunk2_checked,sideChunk3_checked,sideChunk4_checked,sideChunk5_checked,sideChunk6_checked,Bool.true_and]

def haltChunk0 : List HaltWitness := [
  ⟨[8,0,11,0,0,0,0,0,0,0,0,0],2,(2,true)⟩,
  ⟨[8,0,11,0,0,2,0,0,0,0,0,0],3,(0,true)⟩,
  ⟨[8,3,11,0,0,2,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,5,11,0,0,2,0,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,6,11,0,0,2,0,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,7,11,0,0,2,0,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,9,11,0,0,2,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,10,11,0,0,2,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,11,11,0,0,2,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,12,11,0,0,2,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,13,11,0,0,2,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,14,11,0,0,2,0,0,0,0,0,0],4,(3,false)⟩
]
theorem haltChunk0_checked : haltChunk0.all HaltWitness.check = true := by decide

def haltChunk1 : List HaltWitness := [
  ⟨[8,15,11,0,0,2,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,16,11,0,0,2,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,3,0,0,0,0,0,0],4,(1,true)⟩,
  ⟨[8,0,11,1,0,3,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,2,0,3,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,3,0,3,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,4,0,3,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,5,0,3,0,0,0,0,0,0],7,(2,false)⟩,
  ⟨[8,0,11,6,0,3,0,0,0,0,0,0],7,(2,false)⟩,
  ⟨[8,0,11,7,0,3,0,0,0,0,0,0],7,(2,false)⟩,
  ⟨[8,0,11,8,0,3,0,0,0,0,0,0],8,(0,true)⟩,
  ⟨[8,0,11,10,0,3,0,0,0,0,0,0],8,(2,false)⟩
]
theorem haltChunk1_checked : haltChunk1.all HaltWitness.check = true := by decide

def haltChunk2 : List HaltWitness := [
  ⟨[8,0,11,12,0,3,0,0,0,0,0,0],6,(0,true)⟩,
  ⟨[8,0,11,13,0,3,0,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,14,0,3,0,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,15,0,3,0,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,16,0,3,0,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,0,0,4,0,0,0,0,0,0],3,(0,true)⟩,
  ⟨[8,3,11,0,0,4,0,0,0,0,0,0],6,(1,true)⟩,
  ⟨[8,5,11,0,0,4,0,0,0,0,0,0],4,(1,true)⟩,
  ⟨[8,6,11,0,0,4,0,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,7,11,0,0,4,0,0,0,0,0,0],4,(1,true)⟩,
  ⟨[8,10,11,0,0,4,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,12,11,0,0,4,0,0,0,0,0,0],4,(2,false)⟩
]
theorem haltChunk2_checked : haltChunk2.all HaltWitness.check = true := by decide

def haltChunk3 : List HaltWitness := [
  ⟨[8,13,11,0,0,4,0,0,0,0,0,0],4,(3,true)⟩,
  ⟨[8,14,11,0,0,4,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,15,11,0,0,4,0,0,0,0,0,0],4,(3,true)⟩,
  ⟨[8,16,11,0,0,4,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,5,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,2,5,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,0,3,5,0,0,0,0,0,0],6,(1,true)⟩,
  ⟨[8,0,11,0,4,5,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,0,6,5,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,8,5,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,12,5,0,0,0,0,0,0],6,(1,true)⟩,
  ⟨[8,0,11,0,13,5,0,0,0,0,0,0],5,(3,false)⟩
]
theorem haltChunk3_checked : haltChunk3.all HaltWitness.check = true := by decide

def haltChunk4 : List HaltWitness := [
  ⟨[8,0,11,0,14,5,0,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,0,15,5,0,0,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,16,5,0,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,0,0,6,0,0,0,0,0,0],3,(1,true)⟩,
  ⟨[8,0,11,3,0,6,0,0,0,0,0,0],6,(0,true)⟩,
  ⟨[8,0,11,5,0,6,0,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,6,0,6,0,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,7,0,6,0,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,9,0,6,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,10,0,6,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,11,0,6,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,12,0,6,0,0,0,0,0,0],4,(2,false)⟩
]
theorem haltChunk4_checked : haltChunk4.all HaltWitness.check = true := by decide

def haltChunk5 : List HaltWitness := [
  ⟨[8,0,11,13,0,6,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,14,0,6,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,15,0,6,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,16,0,6,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,7,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,2,7,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,0,3,7,0,0,0,0,0,0],6,(1,true)⟩,
  ⟨[8,0,11,0,4,7,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,0,6,7,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,8,7,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,12,7,0,0,0,0,0,0],6,(1,true)⟩,
  ⟨[8,0,11,0,13,7,0,0,0,0,0,0],5,(3,false)⟩
]
theorem haltChunk5_checked : haltChunk5.all HaltWitness.check = true := by decide

def haltChunk6 : List HaltWitness := [
  ⟨[8,0,11,0,14,7,0,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,0,15,7,0,0,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,16,7,0,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,0,0,8,0,0,0,0,0,0],3,(1,true)⟩,
  ⟨[8,0,11,1,0,8,0,0,0,0,0,0],4,(0,true)⟩,
  ⟨[8,0,11,3,0,8,0,0,0,0,0,0],4,(0,true)⟩,
  ⟨[8,0,11,5,0,8,0,0,0,0,0,0],6,(2,false)⟩,
  ⟨[8,0,11,6,0,8,0,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,7,0,8,0,0,0,0,0,0],6,(2,false)⟩,
  ⟨[8,0,11,10,0,8,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,12,0,8,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,13,0,8,0,0,0,0,0,0],4,(3,true)⟩
]
theorem haltChunk6_checked : haltChunk6.all HaltWitness.check = true := by decide

def haltChunk7 : List HaltWitness := [
  ⟨[8,0,11,14,0,8,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,15,0,8,0,0,0,0,0,0],4,(3,true)⟩,
  ⟨[8,0,11,16,0,8,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,9,0,0,0,0,0,0],3,(2,false)⟩,
  ⟨[8,0,11,0,2,9,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,3,9,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,4,9,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,6,9,0,0,0,0,0,0],6,(1,true)⟩,
  ⟨[8,0,11,0,13,9,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,14,9,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,15,9,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,16,9,0,0,0,0,0,0],4,(3,false)⟩
]
theorem haltChunk7_checked : haltChunk7.all HaltWitness.check = true := by decide

def haltChunk8 : List HaltWitness := [
  ⟨[8,0,11,0,0,10,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,3,10,0,0,0,0,0,0],6,(1,true)⟩,
  ⟨[8,0,11,0,6,10,0,0,0,0,0,0],7,(1,true)⟩,
  ⟨[8,0,11,0,13,10,0,0,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,14,10,0,0,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,15,10,0,0,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,16,10,0,0,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,0,11,0,0,0,0,0,0],3,(2,false)⟩,
  ⟨[8,0,11,0,2,11,0,0,0,0,0,0],4,(0,true)⟩,
  ⟨[8,0,11,0,3,11,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,4,11,0,0,0,0,0,0],4,(0,true)⟩,
  ⟨[8,0,11,0,6,11,0,0,0,0,0,0],4,(1,true)⟩
]
theorem haltChunk8_checked : haltChunk8.all HaltWitness.check = true := by decide

def haltChunk9 : List HaltWitness := [
  ⟨[8,0,11,0,8,11,0,0,0,0,0,0],4,(1,true)⟩,
  ⟨[8,0,11,0,13,11,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,14,11,0,0,0,0,0,0],4,(3,true)⟩,
  ⟨[8,0,11,0,15,11,0,0,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,16,11,0,0,0,0,0,0],4,(3,true)⟩,
  ⟨[8,0,11,0,0,12,0,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,1,12,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,0,3,12,0,0,0,0,0,0],5,(0,true)⟩,
  ⟨[8,0,11,0,5,12,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,6,12,0,0,0,0,0,0],7,(1,true)⟩,
  ⟨[8,0,11,0,7,12,0,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,13,12,0,0,0,0,0,0],5,(3,true)⟩
]
theorem haltChunk9_checked : haltChunk9.all HaltWitness.check = true := by decide

def haltChunk10 : List HaltWitness := [
  ⟨[8,0,11,0,14,12,0,0,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,15,12,0,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,0,16,12,0,0,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,0,13,0,0,0,0,0,0],3,(3,false)⟩,
  ⟨[8,0,11,0,0,13,2,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,0,13,3,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,0,13,4,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,0,13,5,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,0,0,13,6,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,0,0,13,7,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,0,0,13,9,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,13,10,0,0,0,0,0],4,(2,false)⟩
]
theorem haltChunk10_checked : haltChunk10.all HaltWitness.check = true := by decide

def haltChunk11 : List HaltWitness := [
  ⟨[8,0,11,0,0,13,11,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,13,12,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,13,14,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,0,0,13,16,0,0,0,0,0],5,(3,true)⟩,
  ⟨[8,0,11,0,0,13,17,0,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,13,18,0,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,13,19,0,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,13,20,0,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,14,0,0,0,0,0,0],3,(3,true)⟩,
  ⟨[8,0,11,0,0,14,0,3,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,0,14,0,5,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,0,0,14,0,6,0,0,0,0],5,(2,false)⟩
]
theorem haltChunk11_checked : haltChunk11.all HaltWitness.check = true := by decide

def haltChunk12 : List HaltWitness := [
  ⟨[8,0,11,0,0,14,0,7,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,0,0,14,0,9,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,14,0,10,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,14,0,11,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,14,0,12,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,14,0,13,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,14,0,14,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,14,0,15,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,14,0,16,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,14,0,17,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,14,0,18,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,14,0,19,0,0,0,0],4,(4,false)⟩
]
theorem haltChunk12_checked : haltChunk12.all HaltWitness.check = true := by decide

def haltChunk13 : List HaltWitness := [
  ⟨[8,0,11,0,0,14,0,20,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,15,0,0,0,0,0,0],3,(3,false)⟩,
  ⟨[8,0,11,0,0,15,2,0,0,0,0,0],4,(0,true)⟩,
  ⟨[8,0,11,0,0,15,3,0,0,0,0,0],5,(1,true)⟩,
  ⟨[8,0,11,0,0,15,4,0,0,0,0,0],4,(0,true)⟩,
  ⟨[8,0,11,0,0,15,5,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,0,0,15,6,0,0,0,0,0],4,(1,true)⟩,
  ⟨[8,0,11,0,0,15,7,0,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,0,0,15,8,0,0,0,0,0],4,(1,true)⟩,
  ⟨[8,0,11,0,0,15,9,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,15,11,0,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,15,12,0,0,0,0,0],5,(3,true)⟩
]
theorem haltChunk13_checked : haltChunk13.all HaltWitness.check = true := by decide

def haltChunk14 : List HaltWitness := [
  ⟨[8,0,11,0,0,15,14,0,0,0,0,0],4,(3,true)⟩,
  ⟨[8,0,11,0,0,15,16,0,0,0,0,0],4,(3,true)⟩,
  ⟨[8,0,11,0,0,15,17,0,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,15,18,0,0,0,0,0],4,(4,true)⟩,
  ⟨[8,0,11,0,0,15,19,0,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,15,20,0,0,0,0,0],4,(4,true)⟩,
  ⟨[8,0,11,0,0,16,0,0,0,0,0,0],3,(3,true)⟩,
  ⟨[8,0,11,0,0,16,0,1,0,0,0,0],4,(0,true)⟩,
  ⟨[8,0,11,0,0,16,0,3,0,0,0,0],4,(0,true)⟩,
  ⟨[8,0,11,0,0,16,0,5,0,0,0,0],4,(1,true)⟩,
  ⟨[8,0,11,0,0,16,0,6,0,0,0,0],5,(2,false)⟩,
  ⟨[8,0,11,0,0,16,0,7,0,0,0,0],4,(1,true)⟩
]
theorem haltChunk14_checked : haltChunk14.all HaltWitness.check = true := by decide

def haltChunk15 : List HaltWitness := [
  ⟨[8,0,11,0,0,16,0,9,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,0,16,0,10,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,16,0,12,0,0,0,0],4,(2,false)⟩,
  ⟨[8,0,11,0,0,16,0,13,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,0,16,0,14,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,16,0,15,0,0,0,0],5,(3,false)⟩,
  ⟨[8,0,11,0,0,16,0,16,0,0,0,0],4,(3,false)⟩,
  ⟨[8,0,11,0,0,16,0,17,0,0,0,0],4,(4,true)⟩,
  ⟨[8,0,11,0,0,16,0,18,0,0,0,0],4,(4,false)⟩,
  ⟨[8,0,11,0,0,16,0,19,0,0,0,0],4,(4,true)⟩,
  ⟨[8,0,11,0,0,16,0,20,0,0,0,0],4,(4,false)⟩
]
theorem haltChunk15_checked : haltChunk15.all HaltWitness.check = true := by decide

def haltData : List HaltWitness := haltChunk0 ++ haltChunk1 ++ haltChunk2 ++ haltChunk3 ++ haltChunk4 ++ haltChunk5 ++ haltChunk6 ++ haltChunk7 ++ haltChunk8 ++ haltChunk9 ++ haltChunk10 ++ haltChunk11 ++ haltChunk12 ++ haltChunk13 ++ haltChunk14 ++ haltChunk15
theorem haltData_checked : haltData.all HaltWitness.check = true := by
  simp only [haltData,List.all_append,haltChunk0_checked,haltChunk1_checked,haltChunk2_checked,haltChunk3_checked,haltChunk4_checked,haltChunk5_checked,haltChunk6_checked,haltChunk7_checked,haltChunk8_checked,haltChunk9_checked,haltChunk10_checked,haltChunk11_checked,haltChunk12_checked,haltChunk13_checked,haltChunk14_checked,haltChunk15_checked,Bool.true_and]

def shallowTables : List PartialMachine :=
  (sideData.map fun w => unpackTable w.table) ++ haltData.map HaltWitness.closed

theorem shallow_safe (p : PartialMachine) (hp : p ∈ shallowTables)
    (m : Machine) (hm : compatible p m) : WeightedBound 7014 m := by
  rcases List.mem_append.mp hp with hs | hh
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hs
    exact w.sound (List.all_eq_true.mp sideData_checked w hw) m hm
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hh
    exact w.sound (List.all_eq_true.mp haltData_checked w hw) m hm

def shallowOrbitTables : List PartialMachine :=
  perms.flatMap fun e => shallowTables.map (pullback e)

theorem shallow_orbit_safe (B : Nat) (hB : 7014 ≤ B)
    (m : Machine) (hp : compatible firstOneB0_1LC m)
    (p : PartialMachine) (hq : p ∈ shallowOrbitTables)
    (hm : compatible p m) : WeightedBound B m := by
  obtain ⟨e,he,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hq
  apply weighted_rename_back B e m (perms_fix_zero e he)
    (firstOne_terminal firstOneB0_1LC (by decide) m hp)
  have hb := shallow_safe q hq (renameTable e m) (compatible_pullback e q m hm)
  intro k d hk hd
  exact Nat.le_trans (hb k d hk hd) hB

def combinedTables : List PartialMachine :=
  orbitTables ++ shallowOrbitTables

theorem combined_safe (B : Nat) (hB : 7014 ≤ B)
    (m : Machine) (hp : compatible firstOneB0_1LC m)
    (p : PartialMachine) (hq : p ∈ combinedTables)
    (hm : compatible p m) : WeightedBound B m := by
  rcases List.mem_append.mp hq with h | h
  · exact side_orbit_safe B hB m hp p h hm
  · exact shallow_orbit_safe B hB m hp p h hm

theorem combined_dichotomy (B : Nat) (hB : 7014 ≤ B)
    (m : Machine) (hp : compatible firstOneB0_1LC m) :
    WeightedBound B m ∨ ∀ p ∈ combinedTables, ¬ compatible p m := by
  by_cases h : ∃ p ∈ combinedTables, compatible p m
  · obtain ⟨p,hq,hm⟩ := h
    exact Or.inl (combined_safe B hB m hp p hq hm)
  · exact Or.inr (fun p hq hm => h ⟨p,hq,hm⟩)

theorem combined_cover (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ m, compatible firstOneB0_1LC m →
      (∀ p ∈ combinedTables, ¬ compatible p m) → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC := by
  apply Cover.leaf
  intro m hm
  rcases combined_dichotomy B hB m hm with h | h
  · exact h
  · exact hOpen m hm h

#print axioms HaltWitness.sound
#print axioms sideData_checked
#print axioms haltData_checked
#print axioms shallow_safe
#print axioms shallow_orbit_safe
#print axioms combined_dichotomy
#print axioms combined_cover
end BB6.Agent49Raw10Shallow

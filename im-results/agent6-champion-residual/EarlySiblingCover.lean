import FastFAR
import SideCycle
import WeightedTNF

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent6EarlySiblings
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent50SideCycle

structure SideWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int

/-- Nine disjoint early raw139 siblings, not in the original frontier witness list. -/
def sideWitnesses : List SideWitness :=
  [⟨[7,24,11,24,14,24,24,16,16,11,24,24],7,1,false,-1⟩,
   ⟨[7,24,11,24,14,24,24,16,18,11,24,24],7,1,false,-1⟩,
   ⟨[7,24,11,24,14,24,8,16,12,11,24,24],8,2,false,-2⟩,
   ⟨[7,24,11,24,14,24,10,16,12,11,24,24],8,2,false,-2⟩,
   ⟨[7,24,11,24,14,24,12,16,12,11,24,24],8,1,false,-2⟩,
   ⟨[7,24,11,24,14,24,13,16,12,11,24,24],18,1,true,0⟩,
   ⟨[7,24,11,24,14,24,14,16,12,11,24,24],8,1,false,-2⟩,
   ⟨[7,24,11,24,14,24,16,16,12,11,24,24],7,2,false,-1⟩,
   ⟨[7,24,11,24,14,24,18,16,12,11,24,24],7,2,false,-1⟩]

def sideOK (w : SideWitness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (FAR.fromCodes w.codes) w.entry w.period w.right w.boundary

theorem side_checked : sideWitnesses.all sideOK = true := by decide

theorem cover_side (B : Nat) (w : SideWitness) (hw : w ∈ sideWitnesses) :
    Cover (WeightedBound B) (FAR.fromCodes w.codes) := by
  have h := List.all_eq_true.mp side_checked w hw
  have hh : 0 < w.period ∧ fastSideCycleCheck (FAR.fromCodes w.codes)
      w.entry w.period w.right w.boundary = true := by
    simpa only [sideOK,Bool.and_eq_true,decide_eq_true_eq] using h
  exact .leaf _ (fun m hm => weighted_never B m
    (fastSideCycleCheck_sound _ _ _ _ _ hh.1 hh.2 m hm))

def farRC : PartialMachine := FAR.fromCodes [7,24,11,24,14,11,3,16,12,11,24,24]
def farRE : PartialMachine := FAR.fromCodes [7,24,11,24,14,19,3,16,12,11,24,24]

def rcData : FAR.Data 2 :=
  ⟨0,[0,1,0,1],[128,256,4096,64,128,4096,128,256,256,64,256,4096,4096],
   [4096,4096,256,256,256,4096,4096,4096,256,256,256,4096,4096],6180⟩

def reData : FAR.Data 2 :=
  ⟨0,[0,1,0,1],[128,256,4096,64,128,4096,128,256,1280,64,1280,4096,4096],
   [4096,4096,1024,1280,256,4096,4096,4096,1024,1280,256,4096,4096],6180⟩

theorem cover_RC (B : Nat) : Cover (WeightedBound B) farRC :=
  .leaf _ (fun m hm => weighted_never B m
    (rcData.sound farRC (rcData.fastValid_sound farRC (by decide)) m hm))

theorem cover_RE (B : Nat) : Cover (WeightedBound B) farRE :=
  .leaf _ (fun m hm => weighted_never B m
    (reData.sound farRE (reData.fastValid_sound farRE (by decide)) m hm))

#print axioms side_checked
#print axioms cover_side
#print axioms cover_RC
#print axioms cover_RE
end BB6.Agent6EarlySiblings

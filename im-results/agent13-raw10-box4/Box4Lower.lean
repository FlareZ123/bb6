import Box4Core
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box4
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent49BoxBridge BB6Coverage.Agent10ZipAudit
open BB6.Agent13.Box17 (zipHalt_sound haltBound haltBound_sound)

def late : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,true,3⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨true,false,1⟩)
  | (2,false) => some (some ⟨false,false,4⟩)
  | (2,true) => some (some ⟨true,true,0⟩)
  | (3,false) => some (some ⟨true,false,5⟩)
  | (3,true) => some (some ⟨false,true,0⟩)
  | (4,false) => some (some ⟨true,true,4⟩)
  | (4,true) => some (some ⟨true,false,3⟩)
  | (5,false) => some (some ⟨false,false,1⟩)
  | (5,true) => some none
  | _ => none

def lateMachine : Machine := fun s => (late s).getD none
theorem lateCompatible : compatible late lateMachine := by
  intro s t h
  simp [lateMachine,h]

theorem lateFits : Fits domain lateMachine := by
  intro s
  obtain ⟨q,b⟩ := s
  revert q b
  decide

theorem lateHalts : HaltsAfter lateMachine 3639 :=
  zipHalt_sound late 3639 (by decide) lateMachine lateCompatible

theorem lateDelayZero : 0 ∈ delays (zeroNext lateMachine) 0 := by decide
theorem lateBound : haltBound late 3639 3640 = true := by decide

theorem lowerBound (B : Nat) (h : ∀ m, Fits raw10Remainder[4]! m → WeightedBound B m) :
    3640 ≤ B :=
  h lateMachine (sourceDomainEq ▸ lateFits) 3639 0 lateHalts lateDelayZero

theorem exact_of_slices (h : ∀ t : Fin 12, 6 ≤ t.val → Good t (root t)) (B : Nat) :
    (∀ m, Fits raw10Remainder[4]! m → WeightedBound B m) ↔ 3640 ≤ B := by
  constructor
  · exact lowerBound B
  · intro hb m hm k d hk hd
    exact Nat.le_trans (source_upper h m hm k d hk hd) hb

#print axioms lowerBound
#print axioms exact_of_slices
end BB6.Agent13.Box4

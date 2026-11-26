import Box17AuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box17
open BB6Coverage BB6.Agent13BlankDelay
-- A0=1RB A1=0LC B0=1LC B1=0RB C0=0LE C1=0LD D0=1LC D1=halt E0=0RA E1=1LF F0=1LA F1=0RC
def late : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,false,2⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨false,true,1⟩)
  | (2,false) => some (some ⟨false,false,4⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨true,false,2⟩)
  | (3,true) => some none
  | (4,false) => some (some ⟨false,true,0⟩)
  | (4,true) => some (some ⟨true,false,5⟩)
  | (5,false) => some (some ⟨true,false,0⟩)
  | (5,true) => some (some ⟨false,true,2⟩)
  | _ => none
theorem lateDelays : possibleDelays late 0 = [0,1,2] := by decide
theorem lateBound : haltBound late 7011 7014 = true := by decide
def lateMachine : Machine := fun s => (late s).getD none
theorem lateCompatible : compatible late lateMachine := by
  intro s t h
  simp [lateMachine,h]
theorem lateFits : BB6.Agent49Box.Fits domain lateMachine := by
  intro s
  obtain ⟨q,b⟩ := s
  revert q b
  decide
theorem lateHalts : HaltsAfter lateMachine 7011 := zipHalt_sound late 7011 (by decide) lateMachine lateCompatible
theorem lateDelayTwo : 2 ∈ delays (zeroNext lateMachine) 0 := by decide
theorem lowerBound (B : Nat) (h : ∀ m, BB6.Agent49Box.Fits domain m → WeightedBound B m) : 7014 ≤ B :=
  h lateMachine lateFits 7011 2 lateHalts lateDelayTwo
#print axioms lowerBound
end BB6.Agent13.Box17

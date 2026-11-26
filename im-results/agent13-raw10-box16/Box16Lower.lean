import Box16Core
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box16
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent13.Box17
def late : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some none
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨false,true,1⟩)
  | (2,false) => some (some ⟨false,false,4⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨true,false,2⟩)
  | (3,true) => some (some ⟨false,false,3⟩)
  | (4,false) => some (some ⟨false,true,0⟩)
  | (4,true) => some (some ⟨true,true,5⟩)
  | (5,false) => some (some ⟨true,true,4⟩)
  | (5,true) => some (some ⟨false,false,1⟩)
  | _ => none
theorem lateDelays : possibleDelays late 0 = [0,1,2] := by decide
theorem lateBound : haltBound late 7373 7376 = true := by decide
def lateMachine : Machine := fun s => (late s).getD none
theorem lateCompatible : compatible late lateMachine := by
  intro s t h
  simp [lateMachine,h]
theorem lateFits : BB6.Agent49Box.Fits domain lateMachine := by
  intro s
  obtain ⟨q,b⟩ := s
  revert q b
  decide
theorem lateHalts : HaltsAfter lateMachine 7373 := zipHalt_sound late 7373 (by decide) lateMachine lateCompatible
theorem lateDelayTwo : 2 ∈ delays (zeroNext lateMachine) 0 := by decide
theorem lowerBound (B : Nat) (h : ∀ m, BB6.Agent49Box.Fits domain m → WeightedBound B m) : 7376 ≤ B :=
  h lateMachine lateFits 7373 2 lateHalts lateDelayTwo
#print axioms lowerBound
end BB6.Agent13.Box16

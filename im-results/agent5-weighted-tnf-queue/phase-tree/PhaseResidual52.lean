import PhaseFastHole
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent5PhaseResidual52
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseFastHole
def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,3⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,4⟩)
  | (2,false) => some (some ⟨false,false,0⟩)
  | (2,true) => some (some ⟨false,true,2⟩)
  | (3,false) => some (some ⟨true,false,0⟩)
  | (3,true) => some (some ⟨true,false,3⟩)
  | (4,false) => none
  | (4,true) => some (some ⟨false,false,5⟩)
  | (5,false) => some (some ⟨true,false,1⟩)
  | (5,true) => some (some ⟨false,false,1⟩)
  | _ => none
theorem firstHole : fastHoleOK 4663 table 4657 (4,false) = true := by decide
theorem safe : ∀ m, compatible table m → WeightedBound 4663 m := last_safe 4663 table 4657 (4,false) (by decide) firstHole (by decide)
#print axioms safe
end BB6.Agent5PhaseResidual52

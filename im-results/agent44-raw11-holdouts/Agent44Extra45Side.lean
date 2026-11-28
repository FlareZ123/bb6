import CachedPhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent44Extra45Side
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,false,2⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def witness : Tree := .side 2051 240 false (-1)
theorem checked : BB6.Agent5CachedPhaseTree.rootCheck 0 p witness = true := by decide +kernel
theorem safe (B : Nat) : ∀ m, compatible p m → WeightedBound B m :=
  BB6.Agent5CachedPhaseTree.sound B p witness (by decide) checked
theorem cover (B : Nat) : Cover (WeightedBound B) p := .leaf _ (safe B)
#print axioms cover
end BB6.Agent44Extra45Side

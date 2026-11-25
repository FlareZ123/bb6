
import CanonicalFrontier
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.RE1REWitness
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | _,_ => none
def witness : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨true,true,4⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,false,5⟩
  | 2,false => some ⟨false,true,3⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,false,0⟩
  | 4,false => some ⟨false,true,1⟩
  | 4,true => some ⟨true,true,4⟩
  | 5,false => some ⟨false,true,0⟩
  | 5,true => some ⟨false,false,5⟩
  | _,_ => none

theorem witness_compatible : compatible p witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : p (_,_) = none := by decide; rw [h] at ht; contradiction
    | cases ht <;> rfl

theorem witness_halts : HaltsAfter witness 163 := by
  constructor <;> rfl

theorem witness_delay : 1 ∈ delays (zeroNext witness) 0 := by decide

theorem lower (B : Nat) (hB : B < 165) : ∃ m, compatible p m ∧ ¬ WeightedBound B m := by
  refine ⟨witness,witness_compatible,?_⟩
  intro hb
  have h := hb 163 1 witness_halts witness_delay
  omega

#print axioms lower
end BB6.Agent19Raw40.RE1REWitness

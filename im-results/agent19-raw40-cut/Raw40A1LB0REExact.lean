import Raw40A1LB0RELate
import Raw40C1LB0REAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Raw40C1LB0RE
open BB6Coverage BB6.Agent13BlankDelay

def witness : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨true,false,1⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨false,true,5⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨false,true,4⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,false,0⟩
  | 4,false => some ⟨false,true,2⟩
  | 4,true => some ⟨true,false,4⟩
  | 5,true => some ⟨true,true,1⟩
  | _,_ => none

theorem witness_compatible : compatible p witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : p (_,_) = none := by decide; rw [h] at ht; contradiction
    | cases ht <;> rfl

theorem witness_halts : HaltsAfter witness 19584 := by
  exact A1LB0RELate.Leaf1922.witness_halts
theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide

theorem exact_weighted : (∀ m, compatible p m → WeightedBound 19585 m) ∧
    ∀ B < 19585, ∃ m, compatible p m ∧ ¬ WeightedBound B m := by
  refine ⟨all, ?_⟩
  intro B hB
  refine ⟨witness, witness_compatible, ?_⟩
  intro hb
  have h := hb 19584 0 witness_halts witness_delay
  omega
#print axioms exact_weighted
end BB6.Agent19Raw40.Raw40C1LB0RE

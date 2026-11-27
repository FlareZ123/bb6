import CheckedLateHole
import Raw36Cut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent29Raw36SharpCounterexample
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit
open BB6.Agent50CheckedLateHole
open BB6.Agent29Raw36

/-- Literal six-state halter extracted from the corrected candidate tree.
    Direct blank simulation independently reaches its only undefined row
    F1 after precisely 1016 executed transitions. -/
def witnessTable : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true  => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true  => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | _,_ => none

abbrev witness : Machine := haltCompletion witnessTable

theorem witness_compatible : compatible branch witness := by
  intro s t h
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases b <;> first | contradiction | (cases h; rfl)

/-- The exact final query, computed independently with the Lean zipper. -/
theorem final_query : zipRead witnessTable 1016 = some (5,true) := by
  decide +kernel

theorem final_hole : witnessTable (5,true) = none := by decide

theorem witness_halts : HaltsAfter witness 1016 :=
  exact_halt witnessTable 1016 (5,true) final_query final_hole

theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide

/-- This formally refutes the obsolete six-hole 162-weight hypothesis:
    any universally valid bound for this original Raw36 descendant is
    at least 1017, irrespective of the unresolved FAR leaves. -/
theorem branch_lower_bound (B : Nat)
    (h : ∀ m, compatible branch m → WeightedBound B m) : 1017 ≤ B :=
  h witness witness_compatible 1016 0 witness_halts witness_delay

theorem no_branch_bound_162 :
    ¬ (∀ m, compatible branch m → WeightedBound 162 m) := by
  intro h
  have hbad := branch_lower_bound 162 h
  omega

#print axioms final_query
#print axioms witness_halts
#print axioms branch_lower_bound
#print axioms no_branch_bound_162

end BB6.Agent29Raw36SharpCounterexample

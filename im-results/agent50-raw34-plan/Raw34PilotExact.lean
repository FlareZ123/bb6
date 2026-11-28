import Raw34Pilot
import Raw34WeightedPlan
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Raw34Pilot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50Raw34Plan

theorem weighted_checked : checkWith nodes [] (weightedCheck 23) 5 0 parent = true := by decide +kernel
theorem cover_weighted : Cover (WeightedBound 23) parent :=
  weightedPlan_closed nodes 23 5 0 parent weighted_checked

def attainerMachine : Machine := fun s => (attainer s).getD none

theorem attained : ∃ m, compatible parent m ∧ HaltsAfter m 22 ∧ 0 ∈ delays (zeroNext m) 0 := by
  have hm : compatible attainer attainerMachine := by
    intro s t ht
    simp [attainerMachine,ht]
  exact ⟨attainerMachine,extendsTable_sound parent attainer (by decide) _ hm,
    finiteHaltCheck_exact attainer 22 attainer_halt _ hm,by decide⟩

#print axioms weighted_checked
#print axioms cover_weighted
#print axioms attained
end BB6.Agent50Raw34Pilot

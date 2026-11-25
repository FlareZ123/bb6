import Lean.Elab.Tactic.Omega
import HardRootLeaves

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19HardRoot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath

/-- The checked first-hole path fixes the first undefined transition at
    primitive step 23. Convert that concrete known-run witness to the
    upstream HaltsAfter predicate. -/
theorem D3_haltsAfter23 : HaltsAfter D3 23 := by
  rw [← forgetHaltRows_defaultCompletion D3]
  apply (weightedTNF_halt_iff_firstHole
    (forgetHaltRows D3) (forgetHaltRows_noAssignedHalt D3) 23).2
  have hrun : knownRun (forgetHaltRows D3) 23 ≠ none := by
    decide
  cases hc : knownRun (forgetHaltRows D3) 23 with
  | none => exact False.elim (hrun hc)
  | some c =>
      refine ⟨c, hc, ?_⟩
      have hhole :
          (forgetHaltRows D3)
            (readSlot ((knownRun (forgetHaltRows D3) 23).getD default)) = none := by
        decide
      simpa [hc] using hhole

/-- Determinism makes 23 the only possible first-halting index. -/
theorem D3_halt_bound24 :
    ∀ k, HaltsAfter D3 k → k + 1 ≤ 24 := by
  intro k hk
  have heq := halting_time_unique D3 k 23 hk D3_haltsAfter23
  omega

/-- Every completion of the erased D3 halt row is covered at the exact
    primitive score bound 24. -/
theorem D3_cover24 :
    Cover (WeightedBound 24) (forgetHaltRows D3) :=
  (D3_cover_iff 24).2 D3_halt_bound24

#print axioms D3_haltsAfter23
#print axioms D3_halt_bound24
#print axioms D3_cover24

end BB6.Agent19HardRoot

import CFiniteSafety
import CQuarterBridge

namespace BB6Agent38

/-- Every published blank-reachable counter state has a finite trajectory
    under the copied accelerator, definitionally equal to the original map. -/
theorem source_reach_has_run (s : S) (h : BB6CLine.Reach s) :
    ∃ n, run n (some (5,0,1)) = some s := by
  induction h with
  | init => exact ⟨0,rfl⟩
  | next p q hp ht ih =>
      obtain ⟨n,hn⟩ := ih
      have hstep : nextC p = some q := by
        rw [source_next_agrees]
        exact ht
      refine ⟨n+1,?_⟩
      rw [show n+1 = 1+n by omega,run_add,hn]
      simpa [run,hstep]

/-- Formal exclusion at arbitrary time of the first 15,743 members of
    the exact original Machine C halting gateway family. -/
theorem source_all_thin_indices_le_15742_unreachable (j : Nat)
    (hj : j ≤ 15742) :
    ¬ BB6CLine.Reach (0,2*j,4*j+10) := by
  intro hr
  have ⟨n,hn⟩ := source_reach_has_run _ hr
  exact all_thin_indices_le_15742_unreachable j hj ⟨n,hn⟩

#print axioms source_reach_has_run
#print axioms source_all_thin_indices_le_15742_unreachable
end BB6Agent38

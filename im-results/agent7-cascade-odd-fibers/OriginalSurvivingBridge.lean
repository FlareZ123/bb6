import OriginalNextBridge
import SurvivingExactGate

namespace Agent7Upstream746

open CascadeSource CascadeSweep
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

/-- This theorem talks about the genuine, unchanged upstream Cryptids
highLevelNext orbit, rather than only the copied compressed C-step model. -/
theorem upstream_excludes_surviving_through_47 (n k : Nat)
    (hn : n ≤ 47) (hc : n%6=4 ∨ n%6=5) :
    Agent10Original746.startRun k ≠
      some (.C (4*2^n-n-4) 0) := by
  cases k with
  | zero =>
      simp [Agent10Original746.startRun, highLevelStart]
  | succ k =>
      rw [Agent10Original746.startRun_successor]
      intro h
      exact (CascadeSurvivingGate.no_surviving_reset_through_47 n hn hc)
        (Agent10Original746.run_reaches k _ _ h)

/-- Every indexed fatal reset actually seen from the original Cryptids
blank-root high-level start must have index >=52, in one of two mod-six classes. -/
theorem upstream_surviving_reset_lower_bound (n k : Nat)
    (hr : Agent10Original746.startRun k =
      some (.C (4*2^n-n-4) 0)) :
    52 ≤ n ∧ (n%6=4 ∨ n%6=5) := by
  cases k with
  | zero =>
      simp [Agent10Original746.startRun, highLevelStart] at hr
  | succ k =>
      rw [Agent10Original746.startRun_successor] at hr
      have hreach : ReachC (2,0) (4*2^n-n-4,0) :=
        Agent10Original746.run_reaches k _ _ hr
      have hmod : n%6=4 ∨ n%6=5 := by
        by_cases hc : n%6=4 ∨ n%6=5
        · exact hc
        · have ho : n%6=0∨n%6=1∨n%6=2∨n%6=3 := by omega
          exact False.elim ((CascadeSmallFatal.all_four_class_indices n ho) hreach)
      have hn : 52 ≤ n := by
        by_cases hg : 52 ≤ n
        · exact hg
        · have hsmall : n ≤ 47 := by omega
          exact False.elim
            ((CascadeSurvivingGate.no_surviving_reset_through_47 n hsmall hmod) hreach)
      exact ⟨hn,hmod⟩

#print axioms upstream_excludes_surviving_through_47
#print axioms upstream_surviving_reset_lower_bound

end Agent7Upstream746

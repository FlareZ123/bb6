import CFiniteSafetyBridge
import CJumpWitnessBridge

namespace BB6Agent38

/-- Any finite run in the copied exact Machine C map gives a true
    inductive reachability implication in the unmodified source. -/
theorem source_reach_after_run (s t : S) (n : Nat)
    (hs : BB6CLine.Reach s) (hr : run n (some s) = some t) :
    BB6CLine.Reach t := by
  exact source_reach_of_run n s t (by simpa only [source_run_agrees] using hr) hs

/-- From any reset gateway the next exact return is the thin line with
    the SAME parameter j. -/
theorem reset_hits_thin (j : Nat) (hj : 1 ≤ j) :
    run (2*j) (some (2*j+1,3*j+4,0)) = some (0,2*j,4*j+10) := by
  have hfirst : nextC (2*j+1,3*j+4,0) = some (2*j-1,1,6*j+9) := by
    cases j with
    | zero => omega
    | succ q =>
        have he : 2*(q+1)+1 = (2*q+1)+2 := by omega
        rw [he]
        simp [nextC]
        omega
  have hsweep : run (2*j-1) (some (2*j-1,1,6*j+9)) =
      some (0,2*j,4*j+10) := by
    have hs := run_sweep (2*j-1) (2*j-1) 1 (6*j+9) (by omega) (by omega)
    have ha : 2*j-1-(2*j-1) = 0 := by omega
    have hk : 1+(2*j-1)=2*j := by omega
    have hc : 6*j+9-(2*j-1)=4*j+10 := by omega
    simpa only [ha,hk,hc] using hs
  calc
    run (2*j) (some (2*j+1,3*j+4,0)) =
        run ((2*j-1)+1) (some (2*j+1,3*j+4,0)) := by
          congr 1
          omega
    _ = run (2*j-1) (run 1 (some (2*j+1,3*j+4,0))) := by
          exact run_add (2*j-1) 1 _
    _ = run (2*j-1) (some (2*j-1,1,6*j+9)) := by
          simp only [run, Option.bind_some, hfirst]
    _ = some (0,2*j,4*j+10) := hsweep

/-- The surviving side gateway family also reaches the thin line,
    indexed j=4m+2 after one high-sweep return. -/
theorem side_hits_thin (m : Nat) :
    run (8*m+3) (some (0,4*m,24*m+23)) =
      some (0,2*(4*m+2),4*(4*m+2)+10) := by
  have hfirst : nextC (0,4*m,24*m+23) = some (8*m+2,2,24*m+20) := by
    have hpar : (4*m)%2 = 0 := by omega
    have hhalf : (4*m)/2=2*m := by omega
    simp [nextC,hpar,hhalf]
    omega
  have hsweep : run (8*m+2) (some (8*m+2,2,24*m+20)) =
      some (0,2*(4*m+2),4*(4*m+2)+10) := by
    have hs := run_sweep (8*m+2) (8*m+2) 2 (24*m+20)
      (by omega) (by omega)
    have ha : 8*m+2-(8*m+2)=0 := by omega
    have hk : 2+(8*m+2)=2*(4*m+2) := by omega
    have hc : 24*m+20-(8*m+2)=4*(4*m+2)+10 := by omega
    simpa only [ha,hk,hc] using hs
  rw [show 8*m+3=(8*m+2)+1 by omega,run_add]
  simpa [run,hfirst] using hsweep

/-- Transferred all-time finite family in the original source:
    reset targets of indices 1 through 15742 are impossible. -/
theorem source_reset_indices_le_15742_unreachable (j : Nat)
    (hj0 : 1 ≤ j) (hj : j ≤ 15742) :
    ¬ BB6CLine.Reach (2*j+1,3*j+4,0) := by
  intro hr
  have hh := source_reach_after_run _ _ (2*j) hr (reset_hits_thin j hj0)
  exact source_all_thin_indices_le_15742_unreachable j hj hh

/-- Original source's side gateways of indices 0 through 3935
    are impossible at EVERY time (not merely within the trace horizon). -/
theorem source_side_indices_le_3935_unreachable (m : Nat)
    (hm : m ≤ 3935) :
    ¬ BB6CLine.Reach (0,4*m,24*m+23) := by
  intro hr
  have hh := source_reach_after_run _ _ (8*m+3) hr (side_hits_thin m)
  apply source_all_thin_indices_le_15742_unreachable (4*m+2) (by omega)
  exact hh

#print axioms source_reset_indices_le_15742_unreachable
#print axioms source_side_indices_le_3935_unreachable
end BB6Agent38

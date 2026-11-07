import Agent8MachineLogHaltSource
import Agent8LogRightParentSource

/-!
Final current original-machine-level #623 halting reduction: a hypothetical
true blank-origin halt yields a pair of adjacent actual accelerated section
visits outside the logarithmic outer and right-tail two-step safety
predicates, outside the five root gate budgets, and within the previously
source-authenticated terminal power-of-three gap. This is necessary only.
-/

namespace BB6.Agent8MachineFullGateSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem target_halt_implies_full_paired_gate
    (hhalt : BusyBeaver.IsHalt target) :
    ∃ m p q a d,
      BB6.Agent49ParitySource.run m=some (.D p q) ∧
      highLevelNext (.D p q)=some (.D a d) ∧
      highLevelNext (.D a d)=none ∧
      0<p ∧ 0<a ∧
      (∀ k, ¬ BB6.Agent8LogParentSource.logOuterBudget p q k) ∧
      (∀ k ell, ¬ BB6.Agent8LogRightParentSource.rightLogBudget p q k ell) ∧
      (∀ k, ¬ BB6.Agent8GateCompleteSource.gateBudget p q k) ∧
      (q%2=1 → q<16*p ∧ p<16*q+68) ∧
      (q%2=0 → q<14*p+24 ∧ p<16*q+44) ∧
      (3^(d-a-5)≤2*(a+d)+5 ∧ 3^(a-d-5)≤2*(a+d)+5) := by
  obtain ⟨m,p,q,a,d,hseen,hstep,hstop,hppos,hapos,
    hlog,hbudget,hodd,heven,hgate⟩ :=
    BB6.Agent8MachineLogHaltSource.target_halt_implies_log_paired_gate hhalt
  have hright := BB6.Agent8LogRightParentSource.blank_terminal_excludes_right_log
    m p q a d hseen hstep hstop
  exact ⟨m,p,q,a,d,hseen,hstep,hstop,hppos,hapos,
    hlog,hright.2,hbudget,hodd,heven,hgate⟩

#print axioms target_halt_implies_full_paired_gate
end BB6.Agent8MachineFullGateSource

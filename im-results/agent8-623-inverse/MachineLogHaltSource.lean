import Agent8MachineHaltSource
import Agent8LogParentSource

/-!
Unmodified Cryptids six-state machine #623: halting implies a genuine
pair of adjacent source-section states satisfying both sharp ternary fatal
conditions and the four logarithmic parent-sector exclusions at all k.
This is a necessary condition and does not assert halting or nonhalting.
-/

namespace BB6.Agent8MachineLogHaltSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem target_halt_implies_log_paired_gate
    (hhalt : BusyBeaver.IsHalt target) :
    ∃ m p q a d,
      BB6.Agent49ParitySource.run m = some (.D p q) ∧
      highLevelNext (.D p q)=some (.D a d) ∧
      highLevelNext (.D a d)=none ∧
      0<p ∧ 0<a ∧
      (∀ k, ¬ BB6.Agent8LogParentSource.logOuterBudget p q k) ∧
      (∀ k, ¬ BB6.Agent8GateCompleteSource.gateBudget p q k) ∧
      (q%2=1 → q<16*p ∧ p<16*q+68) ∧
      (q%2=0 → q<14*p+24 ∧ p<16*q+44) ∧
      (3^(d-a-5)≤2*(a+d)+5 ∧ 3^(a-d-5)≤2*(a+d)+5) := by
  obtain ⟨m,p,q,a,d,hseen,hstep,hstop,hppos,hapos,
    hodd,heven,hbudget,_,_,_,hgate⟩ :=
    BB6.Agent8MachineHaltSource.target_halt_implies_paired_terminal_gate hhalt
  have hlog := BB6.Agent8LogParentSource.blank_terminal_excludes_log
    m p q a d hseen hstep hstop
  exact ⟨m,p,q,a,d,hseen,hstep,hstop,hppos,hapos,
    hlog.2,hbudget,hodd,heven,hgate⟩

#print axioms target_halt_implies_log_paired_gate
end BB6.Agent8MachineLogHaltSource

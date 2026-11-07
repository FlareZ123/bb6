import Agent8HaltParentSource

/-!
Original six-state Busy Beaver machine #623, not merely a synthetic source
accelerator, halting implies a paired source section witness. The terminal
section obeys the established ternary and power gaps, while its immediate
predecessor obeys new explicit angular and five-budget exclusions.

No assertion of halting or nonhalting is made.
-/

namespace BB6.Agent8MachineHaltSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

/-- Any halt of the actual original six-state target yields a *pair*
of genuine blank-root section visits constrained by both halting-gate
and predecessor two-step source theorems. -/
theorem target_halt_implies_paired_terminal_gate
    (hhalt : BusyBeaver.IsHalt target) :
    ∃ m p q a d, run m=some (.D p q) ∧
      highLevelNext (.D p q)=some (.D a d) ∧
      highLevelNext (.D a d)=none ∧
      0<p ∧ 0<a ∧
      (q%2=1 → q<16*p ∧ p<16*q+68) ∧
      (q%2=0 → q<14*p+24 ∧ p<16*q+44) ∧
      (∀ k, ¬ BB6.Agent8GateCompleteSource.gateBudget p q k) ∧
      (a≤d → ternaryOnes (d+1-a)≤a) ∧
      (d%2=1 → a<d+5 ∨ ternaryOnes (a-d-5)<d+3) ∧
      (d%2=0 → a<d+3 ∨ ternaryOnes (a-d-2)<d+2) ∧
      (3^(d-a-5) ≤ 2*(a+d)+5 ∧ 3^(a-d-5) ≤ 2*(a+d)+5) := by
  obtain ⟨n,a,d,hseen,hstop,hpos,hleft,hodd,heven⟩ :=
    BB6.Agent49ParitySource.target_halt_implies_ones_gate hhalt
  obtain ⟨m,p,q,hvisit,hstep,hppos,hpcodd,hpceven,hbudget,hpow⟩ :=
    BB6.Agent8HaltParentSource.blank_terminal_halt_with_parent
      n a d hseen hstop
  exact ⟨m,p,q,a,d,hvisit,hstep,hstop,hppos,hpos,
    hpcodd,hpceven,hbudget,hleft,hodd,heven,hpow⟩

#print axioms target_halt_implies_paired_terminal_gate
end BB6.Agent8MachineHaltSource

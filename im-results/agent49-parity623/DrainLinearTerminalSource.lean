import Agent49DrainLinearLogSource
import Agent8TerminalIntervalSource

/-!
DRAFT: sharper terminal-parent interval obtained by combining the
linear-logarithmic B-drain upper bound and the logarithmic first-counter
loss bound with the existing source one-step terminal gate.

This is an intermediate source draft awaiting Lean CI.
-/

namespace BB6.Agent49DrainLinearTerminalSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DrainFirstSharpSource
open BB6.Agent8DrainSevenSource
open BB6.Agent8BudgetSource
open BB6.Agent49DrainLinearLogSource

/-- A successful drain that is followed by a halting daughter must have
its input first counter within a logarithmic-width interval around d+3b. -/
theorem drainB_terminal_interval_linear (a b d n aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (hb : b<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none) :
    3^((d+3*b)-(a+n)-5) ≤ 2*(a+d+3*b+5*n+2)+5 ∧
    3^(a-d-3*b-5*n-8) ≤ 2*(a+d+3*b+5*n+2)+5 := by
  have hf := drainB_first_le_pow n a b d aa dd hb hs
  have hl := drainB_first_lower_log n a b d aa dd hb hs
  have hd := drainB_d3 b a d aa dd hs
  have hu := drainB_upper_linear_log n a b d aa dd hb hs
  have hg := BB6.Agent49ParitySource.next_none_requires_pow_gap aa dd he hhalt
  have hm : aa+dd ≤ a+d+3*b+5*n+2 := by omega
  constructor
  · have hr : (d+3*b)-(a+n)-5 ≤ dd-aa-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega
  · have hr : (a-d-3*b-5*n-8) ≤ aa-dd-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega

#print axioms drainB_terminal_interval_linear
end BB6.Agent49DrainLinearTerminalSource

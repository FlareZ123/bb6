import Agent8LogRightSource

/-!
Universal source #623 necessary halting intervals through a successful
complete B-drain. The theorem composes sharp output envelopes and the
true source power-of-three one-step terminal gate, giving a preimage
restriction with no synthetic-fuel assumptions or numerical cutoff.
It does not decide genuine blank-root reachability or machine halting.
-/

namespace BB6.Agent8TerminalIntervalSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8GateRepulsionSource
open BB6.Agent8DrainFirstSharpSource
open BB6.Agent8DrainSevenSource
open BB6.Agent8BudgetSource

theorem drainB_terminal_interval (a b d k aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (hb : b<3^k)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none) :
    3^((d+3*b)-(a+k)-5) ≤ 2*(a+k+d+7*b)+5 ∧
    3^((a-b)-(d+7*b)-5) ≤ 2*(a+k+d+7*b)+5 := by
  have hf := drainB_first_le_pow k a b d aa dd hb hs
  have hl := drainB_first_lower_sharp b a d aa dd hs
  have hd := drainB_d3 b a d aa dd hs
  have hu := drainB_third_upper_seven b a d aa dd hs
  have hg := BB6.Agent49ParitySource.next_none_requires_pow_gap aa dd he hhalt
  have hm : aa+dd ≤ a+k+d+7*b := by omega
  constructor
  · have hr : (d+3*b)-(a+k)-5 ≤ dd-aa-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega
  · have hr : (a-b)-(d+7*b)-5 ≤ aa-dd-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega

#print axioms drainB_terminal_interval
end BB6.Agent8TerminalIntervalSource

import Agent8LogConeSource
import Agent8GateRepulsionSource

/-!
Logarithmic right-tail source guarantee for Cryptids #623, using the
original ternary-one budget and parity of all successful B-drain outputs.
These are all-input sufficient conditions, not a blank-root decision.
-/

namespace BB6.Agent8LogRightSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8LogConeSource
open BB6.Agent8GateRepulsionSource
open BB6.Agent8BudgetSource

theorem next_safe_right_log (a d ell : Nat)
    (he : a%2=0) (hgap : a+ell≤d) (hpower : 2*a+3≤3^ell) :
    ∃aa dd, highLevelNext (.D a d) = some (.D aa dd) := by
  by_cases hzero : a=0
  · subst a
    exact next_zero_total d
  · have ha : 0<a := by omega
    have hp := twice_ones_add_one_eq_pow ell
    have hl : a<ternaryOnes ell := by omega
    have hmono := ternaryOnes_mono ell (d+1-a) (by omega)
    exact next_safe_left_ones a d ha he (by omega) (by omega)

theorem drainB_right_log_two_step (a b d k ell aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (he : (a+b)%2=0) (hb : b<3^k)
    (hgap : a+k+ell≤d+3*b)
    (hpower : 2*(a+k)+3≤3^ell) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have hf := drainB_first_le_pow k a b d aa dd hb hs
  have ht := drainB_d3 b a d aa dd hs
  have hp := drainB_parity b a d aa dd hs
  have h0 : aa%2=0 := by omega
  have hh : aa+ell≤dd := by omega
  have hk : 2*aa+3≤3^ell := by omega
  exact next_safe_right_log aa dd ell h0 hh hk

#print axioms next_safe_right_log
#print axioms drainB_right_log_two_step
end BB6.Agent8LogRightSource

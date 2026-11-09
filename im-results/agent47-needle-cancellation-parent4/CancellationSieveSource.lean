import CancellationFiveSource
import CancellationValuationSieve
import Lean.Elab.Tactic.Omega

namespace BB6.Agent47NeedleSieve
open BB6.Agent48.SpaceNeedle
open BB6.Agent47NeedleCancellationFour
open NeedleCancelMod35
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Any original high-level transition into a cancellation feeder obeys
    the exact affine image equation for its incoming valuation. -/
private theorem incoming_equation (r t q : Nat) (hr : 1 ≤ r)
    (h : highLevelNext (.N (oddTower q t)) =
      some (.N (oddTower (CancellationConstructive.feederQ r)
        (CancellationTerminalConstructive.feederV r)))) :
    sourceB r = (2^(t+1)+3)*q + (3*2^t+t+3) := by
  have hformula :
      highLevelNext (.N (oddTower q t)) =
        some (.N (oddTower q t+t+3*(q+1))) := by
    change scanEven (oddTower q t) 0 = _
    simpa using scan_oddTower q t 0
  rw [hformula] at h
  simp only [Option.some.injEq, HighLevelState.N.injEq] at h
  have hfeed := sourceB_is_original_feeder r hr
  have hfactor := oddTower_factor q t
  have halgebra :
      (2^(t+1)+3)*q + (3*2^t+t+3) =
        2^t*(2*q+3)+t+3*(q+1) := by
    rw [Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_add]
    ac_rfl
  rw [halgebra]
  omega

/-- Uniform all-positive-index original-source exclusion for four
    valuation classes modulo twenty. -/
theorem no_cancellation_parent_mod5 (r t : Nat) (hr : 1 ≤ r)
    (ht4 : t%4=0) (ht5 : t%5≠4) :
    ¬∃ q : Nat, highLevelNext (.N (oddTower q t)) =
      some (.N (oddTower (CancellationConstructive.feederQ r)
        (CancellationTerminalConstructive.feederV r))) := by
  rintro ⟨q,h⟩
  have hh := incoming_equation r t q hr h
  exact (CancellationValuationSieve.no_parent_mod5 r t q hr ht4 ht5) hh

/-- Uniform all-positive-index original-source exclusion for four
    valuation classes modulo twenty-one. -/
theorem no_cancellation_parent_mod7 (r t : Nat) (hr : 1 ≤ r)
    (ht3 : t%3=1) (ht7 : t%7≤3) :
    ¬∃ q : Nat, highLevelNext (.N (oddTower q t)) =
      some (.N (oddTower (CancellationConstructive.feederQ r)
        (CancellationTerminalConstructive.feederV r))) := by
  rintro ⟨q,h⟩
  have hh := incoming_equation r t q hr h
  exact (CancellationValuationSieve.no_parent_mod7 r t q hr ht3 ht7) hh

#print axioms no_cancellation_parent_mod5
#print axioms no_cancellation_parent_mod7
end BB6.Agent47NeedleSieve

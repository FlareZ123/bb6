import Lean.Elab.Tactic.Omega
import DRegularSourceShift
import EExceptionalShift

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.EExceptionalAppend
open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.DRegularShift

/-- Append an original-source E exceptional return to all 3-adic lifted
    regular prefixes, preserving physical infinite-tape observation. -/
theorem lifted_exception_source (s : DRegular.L) (k m q p : Nat)
    (hc : DRegular.Canon s)
    (hr : DRegular.run k s = some ⟨3*m+4,q+1,1⟩) :
    ObsEq
      (run
        (DRegular.accumulated k (shiftNat s (3^(k+1)*p)) +
          BB6.Agent32EAll.duration (m+8^k*p) q)
        (DRegularSource.sourceSection (shiftNat s (3^(k+1)*p))))
      (BB6.Agent32EAll.output (m+8^k*p) q []) := by
  have hpow : 3^(k+1)*p = 3^k*(3*p) := by
    simp only [Nat.pow_succ]
    ac_rfl

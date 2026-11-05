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
  have hmid :
      BB6.DRegularSourceShift.outputLift (⟨3*m+4,q+1,1⟩ : DRegular.L) k (3*p) =
      (⟨3*(m+8^k*p)+4,q+1,1⟩ : DRegular.L) := by
    change (⟨3*m+4+8^k*(3*p),q+1,1⟩ : DRegular.L) =
      ⟨3*(m+8^k*p)+4,q+1,1⟩
    congr 1
    have hmul : 8^k*(3*p) = 3*(8^k*p) := by ac_rfl
    rw [hmul]
    omega
  have hroot : ObsEq
      (run (DRegular.accumulated k (shiftNat s (3^(k+1)*p)))
        (DRegularSource.sourceSection (shiftNat s (3^(k+1)*p))))
      (DRegularSource.sourceSection ⟨3*(m+8^k*p)+4,q+1,1⟩) := by
    rw [hpow]
    simpa only [BB6.DRegularSourceShift.inputLift,hmid] using
      (BB6.DRegularSourceShift.lifted_original_run s ⟨3*m+4,q+1,1⟩
        k (3*p) hc hr)
  exact source_chain
    (DRegular.accumulated k (shiftNat s (3^(k+1)*p)))
    (BB6.Agent32EAll.duration (m+8^k*p) q)
    (DRegularSource.sourceSection (shiftNat s (3^(k+1)*p)))
    (DRegularSource.sourceSection ⟨3*(m+8^k*p)+4,q+1,1⟩)
    (BB6.Agent32EAll.output (m+8^k*p) q [])
    hroot (BB6.EExceptionalShift.e_source (m+8^k*p) q)

/-- The exceptional source output preserves its full suffix under all
    3^(k+1) unary lifts, including exceptional q=0 packets. -/
theorem lifted_exception_output (k m q p : Nat) :
    (BB6.Agent32EAll.output (m+8^k*p) q []).r =
       List.replicate (8^(k+1)*p) true ++
         (BB6.Agent32EAll.output m q []).r := by
  have h := BB6.EExceptionalShift.output_shift m q (8^k*p)
  have hp : 8^(k+1)*p=8*(8^k*p) := by
    simp only [Nat.pow_succ]
    ac_rfl
  rw [hp]
  exact h

#print axioms lifted_exception_source
#print axioms lifted_exception_output
end BB6.EExceptionalAppend

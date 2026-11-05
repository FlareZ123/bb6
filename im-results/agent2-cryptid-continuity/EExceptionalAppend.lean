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

/-- Exponential offset conversion used at the irregular exit. -/
private theorem eight_square (k : Nat) : 8^k*8^k=64^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      8^(k+1)*8^(k+1) = (8^k*8^k)*(8*8) := by
        simp only [Nat.pow_succ]
        ac_rfl
      _ = 64^(k+1) := by rw [ih]; simp only [Nat.pow_succ]

private theorem cost_join (D U L Q m k p : Nat) :
    (D+L*(3*p)+Q*(3*p)*(3*p))+
    (U+(24*m+49)*(8^k*p)+12*(8^k*p)*(8^k*p)) =
    (D+U)+(3*L+(24*m+49)*8^k)*p+
      (9*Q+12*64^k)*p*p := by
  have h1 : L*(3*p)=(3*L)*p := by ac_rfl
  have h2 : (24*m+49)*(8^k*p)=((24*m+49)*8^k)*p := by ac_rfl
  have h3 : Q*(3*p)*(3*p)=(9*Q)*p*p := by
    calc
      Q*(3*p)*(3*p) = (3*3*Q)*p*p := by ac_rfl
      _ = (9*Q)*p*p := by rfl
  have h4 : 12*(8^k*p)*(8^k*p)=(12*64^k)*p*p := by
    calc
      12*(8^k*p)*(8^k*p) = (12*(8^k*8^k))*p*p := by ac_rfl
      _ = (12*64^k)*p*p := by rw [eight_square]
  rw [h1,h2,h3,h4]
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

/-- Exact original six-state runtime after k regular source returns plus one
    exceptional E return. The universal quadratic curvature remains
    quadCoeff (k+1), even though DRegular.next itself is undefined at E. -/
theorem lifted_exception_timed (s : DRegular.L) (k m q p : Nat)
    (hc : DRegular.Canon s)
    (hr : DRegular.run k s = some ⟨3*m+4,q+1,1⟩) :
    ObsEq
      (run
        (DRegular.accumulated k s + BB6.Agent32EAll.duration m q +
          (3*BB6.DRegularTimedShift.linearCoeff k s+(24*m+49)*8^k)*p +
          BB6.DRegularTimedShift.quadCoeff (k+1)*p*p)
        (DRegularSource.sourceSection (shiftNat s (3^(k+1)*p))))
      (BB6.Agent32EAll.output (m+8^k*p) q []) := by
  have hsource := lifted_exception_source s k m q p hc hr
  have hacc := BB6.DRegularTimedShift.accumulated_shift k s
    (⟨3*m+4,q+1,1⟩ : DRegular.L) (3*p) hc hr
  have hpow : 3^k*(3*p)=3^(k+1)*p := by
    simp only [Nat.pow_succ]
    ac_rfl
  rw [hpow] at hacc
  have he := BB6.EExceptionalShift.duration_shift m q (8^k*p)
  have htime :
      DRegular.accumulated k (shiftNat s (3^(k+1)*p)) +
        BB6.Agent32EAll.duration (m+8^k*p) q =
      DRegular.accumulated k s + BB6.Agent32EAll.duration m q +
        (3*BB6.DRegularTimedShift.linearCoeff k s+(24*m+49)*8^k)*p +
        BB6.DRegularTimedShift.quadCoeff (k+1)*p*p := by
    calc
      _ = (DRegular.accumulated k s +
              BB6.DRegularTimedShift.linearCoeff k s*(3*p) +
              BB6.DRegularTimedShift.quadCoeff k*(3*p)*(3*p)) +
          (BB6.Agent32EAll.duration m q +
              (24*m+49)*(8^k*p) +12*(8^k*p)*(8^k*p)) := by rw [hacc, he]
      _ = (DRegular.accumulated k s+BB6.Agent32EAll.duration m q) +
            (3*BB6.DRegularTimedShift.linearCoeff k s+(24*m+49)*8^k)*p +
            (9*BB6.DRegularTimedShift.quadCoeff k+12*64^k)*p*p := by
              exact cost_join (DRegular.accumulated k s)
                (BB6.Agent32EAll.duration m q)
                (BB6.DRegularTimedShift.linearCoeff k s)
                (BB6.DRegularTimedShift.quadCoeff k) m k p
      _ = _ := by rw [BB6.DRegularTimedShift.quad_right]
  rw [htime] at hsource
  exact hsource

#print axioms lifted_exception_timed

#print axioms lifted_exception_source
#print axioms lifted_exception_output
end BB6.EExceptionalAppend

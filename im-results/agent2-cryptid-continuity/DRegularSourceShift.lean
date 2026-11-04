import Lean.Elab.Tactic.Omega
import DRegularShift
import DRegularTimedShift
import ERemaining

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.DRegularSourceShift
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- Prepare the SAME canonical right suffix, adding 3^k*p initial unary cells. -/
def inputLift (s : DRegular.L) (k p : Nat) : DRegular.L :=
  BB6.DRegularShift.shiftNat s (3^k*p)

def outputLift (s : DRegular.L) (k p : Nat) : DRegular.L :=
  BB6.DRegularShift.shiftNat s (8^k*p)

private theorem lift_canon (s : DRegular.L) (k p : Nat)
    (hc : DRegular.Canon s) : DRegular.Canon (inputLift s k p) := by
  rcases hc with ⟨ha,hq⟩
  constructor
  · change 2 ≤ s.a + 3^k*p
    omega
  · change s.q ≠ 0 ∨ s.b = 0
    exact hq

private theorem lifted_model (s t : DRegular.L) (k p : Nat)
    (hc : DRegular.Canon s) (hr : DRegular.run k s = some t) :
    DRegular.run k (inputLift s k p) = some (outputLift t k p) := by
  change DRegular.run k (BB6.DRegularShift.shiftNat s (3^k*p)) =
    some (BB6.DRegularShift.shiftNat t (8^k*p))
  have h := BB6.DRegularShift.run_shift k s p hc
  rw [hr] at h
  exact h

/-- For every canonical original six-state F/0 tape in the regular
    language, each 3-adic unary lift executes exactly k authenticated
    SOURCE macro transitions, with a physically correct endpoint at
    unary offset 8^k*p and the UNCHANGED suffix.
    Raw runtimes on either orbit are exact but generally unequal. -/
theorem lifted_original_run (s t : DRegular.L) (k p : Nat)
    (hc : DRegular.Canon s) (hr : DRegular.run k s = some t) :
    ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated k (inputLift s k p))
        (DRegularSource.sourceSection (inputLift s k p)))
      (DRegularSource.sourceSection (outputLift t k p)) := by
  exact DRegular.transport_obs
    CryptidBoundary.run DRegularSource.sourceSection ObsEq
    (fun c => rfl) CryptidBoundary.run_add
    (fun c => cfgEq_refl (represent c))
    (fun x y z h g => cfgEq_trans h g)
    (fun n x y h => source_congr n h)
    BB6.ERemaining.source_contract
    k (inputLift s k p) (outputLift t k p)
    (lift_canon s k p hc) (lifted_model s t k p hc hr)

/-- BOTH the base and lifted source-machine inputs have rigorously
    authenticated finite primitive-step endpoints under exact tape
    observational equality. These are independent physical runs. -/
theorem paired_original_run (s t : DRegular.L) (k p : Nat)
    (hc : DRegular.Canon s) (hr : DRegular.run k s = some t) :
    ObsEq
      (CryptidBoundary.run (DRegular.accumulated k s)
        (DRegularSource.sourceSection s))
      (DRegularSource.sourceSection t) ∧
    ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated k (inputLift s k p))
        (DRegularSource.sourceSection (inputLift s k p)))
      (DRegularSource.sourceSection (outputLift t k p)) := by
  constructor
  · exact DRegular.transport_obs
      CryptidBoundary.run DRegularSource.sourceSection ObsEq
      (fun c => rfl) CryptidBoundary.run_add
      (fun c => cfgEq_refl (represent c))
      (fun x y z h g => cfgEq_trans h g)
      (fun n x y h => source_congr n h)
      BB6.ERemaining.source_contract k s t hc hr
  · exact lifted_original_run s t k p hc hr

#print axioms lifted_model
#print axioms lifted_original_run
#print axioms paired_original_run
end BB6.DRegularSourceShift

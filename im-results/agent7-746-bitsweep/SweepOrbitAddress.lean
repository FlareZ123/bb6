import SweepAddress

namespace CascadeFastReturn
open CascadeBitSweep

/-- Every successful finite root-to-root reset path has nondecreasing
    first-failed dyadic sweep index. This holds from any starting height. -/
theorem runBit_address_monotone (h steps u : Nat)
    (hu : runBit h steps = some u) :
    firstFailIndex h ≤ firstFailIndex u := by
  induction steps generalizing u with
  | zero =>
    simp only [runBit] at hu
    have hv := Option.some.inj hu
    subst u
    omega
  | succ steps ih =>
    cases hs : runBit h steps with
    | none => simp [runBit, hs] at hu
    | some v =>
      have hv : bitOutcome v = some u := by
        simpa [runBit, hs] using hu
      exact Nat.le_trans (ih v hs) (bitOutcome_address_monotone v u hv)

#print axioms runBit_address_monotone
end CascadeFastReturn

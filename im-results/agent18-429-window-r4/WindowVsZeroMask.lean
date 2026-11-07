import WindowLeaf
import ZeroMaskOracle
import FrontierMass
import FiniteDecision

namespace BB429WindowLeaf
open BB6Coverage

/-- The older control-only zero-writer oracle cannot close the oscillatory
four-row cylinder, because the authentic A/0 instruction writes one. -/
theorem oscillator_zeroMaskOracle_false :
    zeroMaskOracle oscillatory = false := by decide

/-- However the full finite-window invariant gives a closed sound
original-blank nonhalting leaf for every completion of this cylinder. -/
theorem oscillator_mass : cylinderMass oscillatory = 25^8 := by decide
theorem oscillator_mass_explicit :
    cylinderMass oscillatory = 152587890625 := by decide

/-- The extant short-halt/fresh-ray/zero-mask combined oracle also
does not close this actual nonhalting cylinder at the global audit
parameters (runtime bound 6, ray discovery horizon 12). -/
theorem oscillator_existing_finite_oracle_false :
    finiteDecisionOracle oscillatory 6 12 = false := by decide

theorem oscillator_not_zero_only_but_closed (bound : Nat) :
    zeroMaskOracle oscillatory = false ∧
    Cover (DecidedBelow bound) oscillatory :=
  ⟨oscillator_zeroMaskOracle_false, oscillator_leaf bound⟩

#print axioms oscillator_existing_finite_oracle_false
#print axioms oscillator_mass
#print axioms oscillator_mass_explicit
#print axioms oscillator_not_zero_only_but_closed
end BB429WindowLeaf

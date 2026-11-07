import WindowLeaf
import ZeroMaskOracle

namespace BB429WindowLeaf
open BB6Coverage

/-- The older control-only zero-writer oracle cannot close the oscillatory
four-row cylinder, because the authentic A/0 instruction writes one. -/
theorem oscillator_zeroMaskOracle_false :
    zeroMaskOracle oscillatory = false := by decide

/-- However the full finite-window invariant gives a closed sound
original-blank nonhalting leaf for every completion of this cylinder. -/
theorem oscillator_not_zero_only_but_closed (bound : Nat) :
    zeroMaskOracle oscillatory = false ∧
    Cover (DecidedBelow bound) oscillatory :=
  ⟨oscillator_zeroMaskOracle_false, oscillator_leaf bound⟩

#print axioms oscillator_not_zero_only_but_closed
end BB429WindowLeaf

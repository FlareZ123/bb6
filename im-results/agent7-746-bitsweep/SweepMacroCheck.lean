import SweepEvenOrbit

namespace CascadeFastReturn
open CascadeBitSweep

/-- Accept any proposed even-reset batch only after an exact arithmetic check;
    otherwise execute precisely one genuine source reset. -/
def macroStep (h k m d : Nat) : Nat × Option Nat :=
  if 0 < m ∧ evenBlockCheck h k m d = true then
    (m, some (atHeight k 0 d))
  else
    (1, bitOutcome h)

/-- A proposed batch is safe for the actual C-reset orbit, even if the
    supplied witness data is arbitrary or adversarial. -/
theorem macroStep_sound (h k m d : Nat) :
    runBit h (macroStep h k m d).1 = (macroStep h k m d).2 := by
  by_cases hc : 0 < m ∧ evenBlockCheck h k m d = true
  · simp only [macroStep, if_pos hc]
    exact evenBlockCheck_sound h k m d hc.2
  · simp [macroStep, hc, runBit]

#print axioms macroStep_sound
end CascadeFastReturn

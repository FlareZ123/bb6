import FiniteHalting
import RayFiniteOracle
import ZeroMaskOracle
namespace BB6Coverage

/-- Combined certified sparse machine leaf: a short halt, or an arbitrary
    finite prefix entering a persistent, pristine, directional ray. -/
def finiteDecisionOracle (p : PartialMachine) (bound rayLimit : Nat) : Bool :=
  (finiteHaltOracle p bound || finiteRayOracle p rayLimit) || zeroMaskOracle p

theorem finiteDecisionOracle_sound (p : PartialMachine) (bound rayLimit : Nat)
    (h : finiteDecisionOracle p bound rayLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hfirst | hz
  · rcases (Bool.or_eq_true _ _).mp hfirst with hh | hn
    · exact finiteHaltOracle_sound p bound hh
    · exact finiteRayOracle_sound p rayLimit bound hn
  · exact zeroMaskOracle_sound p bound hz

theorem turn_decision_leaf : Cover (DecidedBelow 2) turnTable := by
  apply finiteDecisionOracle_sound turnTable 2 2
  decide

theorem halt_decision_leaf : Cover (DecidedBelow 2) twoStepHaltTable := by
  apply finiteDecisionOracle_sound twoStepHaltTable 2 2
  decide

theorem turning_zero_writer_decision_leaf :
    Cover (DecidedBelow 2) turningZeroWriter := by
  apply finiteDecisionOracle_sound turningZeroWriter 2 2
  decide

#print axioms turning_zero_writer_decision_leaf
#print axioms finiteDecisionOracle_sound
#print axioms turn_decision_leaf
#print axioms halt_decision_leaf
end BB6Coverage

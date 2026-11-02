import FiniteHalting
import RayFiniteOracle
namespace BB6Coverage

/-- Combined certified sparse machine leaf: a short halt, or an arbitrary
    finite prefix entering a persistent, pristine, directional ray. -/
def finiteDecisionOracle (p : PartialMachine) (bound rayLimit : Nat) : Bool :=
  finiteHaltOracle p bound || finiteRayOracle p rayLimit

theorem finiteDecisionOracle_sound (p : PartialMachine) (bound rayLimit : Nat)
    (h : finiteDecisionOracle p bound rayLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hh | hn
  · exact finiteHaltOracle_sound p bound hh
  · exact finiteRayOracle_sound p rayLimit bound hn

theorem turn_decision_leaf : Cover (DecidedBelow 2) turnTable := by
  apply finiteDecisionOracle_sound turnTable 2 2
  decide

theorem halt_decision_leaf : Cover (DecidedBelow 2) twoStepHaltTable := by
  apply finiteDecisionOracle_sound twoStepHaltTable 2 2
  decide

#print axioms finiteDecisionOracle_sound
#print axioms turn_decision_leaf
#print axioms halt_decision_leaf
end BB6Coverage

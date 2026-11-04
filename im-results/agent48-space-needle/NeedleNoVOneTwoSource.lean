import NeedleTwoStepOddSource
import NeedleNoVOne
import NeedleNoVTwo
import Lean.Elab.Tactic.Omega
namespace BB6.Agent48.NeedleTwoStepOddBridge
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.NeedleTwoStepOdd
open BB6.Agent48.SpaceNeedle

/-- No source-valid odd-intermediate terminal two-step feeder can start
in the first-step 2-adic valuation-one source sector. -/
theorem no_source_valuation_one (q K : Nat) (hK : 0<K) :
  ¬ (∃ e, highLevelNext (.N (oddTower q 1))=some (.N e) ∧
     e%2=1 ∧ highLevelNext (.N e)=some (.N (2^K-2))) := by
  intro h
  exact no_v_one_odd_terminal q K ((original_two_step_odd_iff q 1 K hK).mp h)

/-- No source-valid odd-intermediate terminal two-step feeder can start
in the first-step 2-adic valuation-two source sector. -/
theorem no_source_valuation_two (q K : Nat) (hK : 0<K) :
  ¬ (∃ e, highLevelNext (.N (oddTower q 2))=some (.N e) ∧
     e%2=1 ∧ highLevelNext (.N e)=some (.N (2^K-2))) := by
  intro h
  exact no_v_two_odd_terminal q K ((original_two_step_odd_iff q 2 K hK).mp h)

#print axioms no_source_valuation_one
#print axioms no_source_valuation_two
end BB6.Agent48.NeedleTwoStepOddBridge

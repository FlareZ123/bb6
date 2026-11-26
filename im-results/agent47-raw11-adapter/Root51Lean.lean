import Root51LeanPart0
import Root51LeanPart1
import Root51LeanPart2
import Root51LeanPart3
import Root51LeanPart4
import Root51LeanPart5
import Root51LeanPart6
import Root51LeanPart7
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent47Root51
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
theorem safe : ∀ m, compatible parent m → WeightedBound 208 m := by
  apply split_safe 208 parent 13 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23
theorem cover : Cover (WeightedBound 208) parent := .leaf _ safe
#print axioms safe
#print axioms cover
end BB6.Agent47Root51

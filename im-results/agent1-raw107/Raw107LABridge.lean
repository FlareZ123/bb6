import Raw107B1LAData
import Raw107LAPairCounter
import Raw107LAUnary
import Raw107LA385

namespace BB6.Agent1Raw107LABridge
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent11Raw107B1LA

/-- Exact order is the original specs_partial.json exception map:
    93,94,95,96,97,98,99,385. Each application is checked against
    the generated partial table via definitional equality. -/
theorem exceptions : Exceptions := by
  intro i m hm
  rcases i with ⟨v,hv⟩
  have he : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BB6.Agent11Raw107LAPairCounter.M93.never m hm
  · exact BB6.Agent11Raw107LAPairCounter.M94.never m hm
  · exact BB6.Agent1Raw107LAUnary.M95.never m hm
  · exact BB6.Agent1Raw107LAUnary.M96.never m hm
  · exact BB6.Agent11Raw107LAPairCounter.M97.never m hm
  · exact BB6.Agent11Raw107LAPairCounter.M98.never m hm
  · exact BB6.Agent1Raw107LAUnary.M99.never m hm
  · exact BB6.Agent10Raw107LA385.never m hm

theorem all_completions : ∀ m, compatible parent m → WeightedBound 282 m :=
  BB6.Agent11Raw107B1LA.all_completions exceptions

#print axioms exceptions
#print axioms all_completions
end BB6.Agent1Raw107LABridge

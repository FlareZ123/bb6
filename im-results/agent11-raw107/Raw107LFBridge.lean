import Raw107B1LFData
import Raw107LF1424
import Raw107LF1655
namespace BB6.Agent10Raw107LFBridge
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent11Raw107B1LF

theorem exceptions : Exceptions := by
  intro i m hm
  rcases i with ⟨v,hv⟩
  have he : v = 0 ∨ v = 1 := by omega
  rcases he with rfl | rfl
  · exact BB6.Agent10Raw107LF1424.never m hm
  · exact BB6.Agent10Raw107LF1655.never m hm

theorem all_completions : ∀ m, compatible parent m → WeightedBound 753 m :=
  BB6.Agent11Raw107B1LF.all_completions exceptions

#print axioms exceptions
#print axioms all_completions
end BB6.Agent10Raw107LFBridge

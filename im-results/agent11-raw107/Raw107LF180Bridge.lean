import Raw107B0LFData
import Raw107LF180
namespace BB6.Agent10Raw107LF180Bridge
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent11Raw107B0LF

theorem exceptions : Exceptions := by
  intro i m hm
  rcases i with ⟨v,hv⟩
  have he : v = 0 := by omega
  subst v
  exact BB6.Agent10Raw107LF180.never m hm

theorem all_completions : ∀ m, compatible parent m → WeightedBound 815 m :=
  BB6.Agent11Raw107B0LF.all_completions exceptions

#print axioms exceptions
#print axioms all_completions
end BB6.Agent10Raw107LF180Bridge

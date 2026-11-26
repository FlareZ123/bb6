import Raw39AcceptedSeven
import Raw391LAComplete

namespace BB6.Agent11Raw39AcceptedEight
open BB6Coverage BB6.Agent11SemanticChunks BB6.Agent13BlankDelay
open BB6.Agent11Raw39AcceptedSix (p39 child)

def remaining : List Move := [⟨false,false,4⟩, ⟨true,false,4⟩, ⟨true,true,4⟩]

theorem remaining_count : remaining.length = 3 := by decide

theorem parent_bound_three (B : Nat) (hB : 2354 ≤ B)
    (h : ∀ mv ∈ remaining, Bound B (child mv)) : Bound B p39 := by
  apply BB6.Agent11Raw39AcceptedSeven.parent_bound_four B hB
  intro mv hm
  simp only [BB6.Agent11Raw39AcceptedSeven.remaining, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact h _ (by decide)
  · intro m hc k d hk hd
    exact Nat.le_trans (BB6.Agent11Raw391LA.all1LA m hc k d hk hd) (by omega)
  · exact h _ (by decide)
  · exact h _ (by decide)

theorem parent_cover_three (B : Nat) (hB : 2354 ≤ B)
    (h : ∀ mv ∈ remaining, Bound B (child mv)) : Cover (WeightedBound B) p39 :=
  .leaf p39 (parent_bound_three B hB h)

#print axioms parent_cover_three
end BB6.Agent11Raw39AcceptedEight

import Raw36D110Live8
import Raw36D110Kid04

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Original-source complete whole-branch Cover for the D1=0RE E0=0LE
eight-hole? Child = D1=0RE + E0=0LE, with 13 original OPEN
literal tables, 12 new FAR proofs and 1 new inverse-stack automaton.
All certificates are kernel-replayed and the remaining seven E0 next
actions are the only assumptions in the source-checked parent theorem.
-/

namespace BB6.Agent29Raw36D110Live7
open BB6Coverage BB6.Agent13BlankDelay

def liveCodes : List Nat := [5,11,12,13,16,17,23]

theorem child04_identity :
    BB6.Agent29Raw36D110Live8.child 4 =
      BB6.Agent29Raw36D110.b1Child ⟨false,false,4⟩ := by rfl

theorem child04_cover :
    Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
      (BB6.Agent29Raw36D110Live8.child 4) := by
  rw [child04_identity]
  apply Cover.leaf
  intro m hm
  exact BB6.Agent29Raw36D110.kid04_bound m hm

theorem live8_from_live7
    (h : ∀ i ∈ liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i)) :
    ∀ i ∈ BB6.Agent29Raw36D110Live8.liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i) := by
  intro i hi
  simp only [BB6.Agent29Raw36D110Live8.liveCodes,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact child04_cover
  · exact h 5 (by decide)
  · exact h 11 (by decide)
  · exact h 12 (by decide)
  · exact h 13 (by decide)
  · exact h 16 (by decide)
  · exact h 17 (by decide)
  · exact h 23 (by decide)

theorem parent_cover_from_live7
    (h : ∀ i ∈ liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i)) :
    Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
      BB6.Agent29Raw36D110Live8.parent := by
  exact BB6.Agent29Raw36D110Live8.parent_cover_from_live8
    (live8_from_live7 h)

theorem live7_count : liveCodes.length = 7 := by decide

#print axioms child04_identity
#print axioms child04_cover
#print axioms live8_from_live7
#print axioms parent_cover_from_live7
#print axioms live7_count
end BB6.Agent29Raw36D110Live7

import Raw36D110Live7AfterE0LE
import Raw36D110Kid13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Second independent complete six-hole next-move child after consuming
D1=0RE / E0=0LE. All 40 previously OPEN E0=1LB literal leaves
receive exact source certificates (16 FAR, 23 prior stack,
one newly discovered 1318-raw/108-compressed-state regular-stack proof).
The six other first-E0 ordinary moves remain explicit Cover hypotheses.
No assertion that the whole D110 parent is bounded is made here.
-/

namespace BB6.Agent29Raw36D110Live6
open BB6Coverage BB6.Agent13BlankDelay

def liveCodes : List Nat := [5,11,12,16,17,23]

theorem child13_identity :
    BB6.Agent29Raw36D110Live8.child 13 =
      BB6.Agent29Raw36D110.b1Child ⟨true,false,1⟩ := by rfl

theorem child13_cover :
    Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
      (BB6.Agent29Raw36D110Live8.child 13) := by
  rw [child13_identity]
  apply Cover.leaf
  intro m hm
  exact BB6.Agent29Raw36D110.kid13_bound m hm

theorem live7_from_live6
    (h : ∀ i ∈ liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i)) :
    ∀ i ∈ BB6.Agent29Raw36D110Live7.liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i) := by
  intro i hi
  simp only [BB6.Agent29Raw36D110Live7.liveCodes,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h 5 (by decide)
  · exact h 11 (by decide)
  · exact h 12 (by decide)
  · exact child13_cover
  · exact h 16 (by decide)
  · exact h 17 (by decide)
  · exact h 23 (by decide)

theorem parent_cover_from_live6
    (h : ∀ i ∈ liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i)) :
    Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
      BB6.Agent29Raw36D110Live8.parent :=
  BB6.Agent29Raw36D110Live7.parent_cover_from_live7
    (live7_from_live6 h)

theorem live6_count : liveCodes.length = 6 := by decide

#print axioms child13_identity
#print axioms child13_cover
#print axioms live7_from_live6
#print axioms parent_cover_from_live6
#print axioms live6_count
end BB6.Agent29Raw36D110Live6

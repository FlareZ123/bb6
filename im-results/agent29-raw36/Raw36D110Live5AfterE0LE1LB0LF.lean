import Raw36D110Live6AfterE0LE1LB
import Raw36D110Kid05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Consume the complete E0=0LF child of the D1=0RE branch after the
source-accepted E0=0LE and E0=1LB children.  The remaining five first-E0
Cover obligations are exactly 0RF, 1LA, 1LE, 1LF and 1RF.
This is a conditional branch reduction, not a complete D1=0RE Cover.
-/

namespace BB6.Agent29Raw36D110Live5
open BB6Coverage BB6.Agent13BlankDelay

def liveCodes : List Nat := [11,12,16,17,23]

theorem child05_identity :
    BB6.Agent29Raw36D110Live8.child 5 =
      BB6.Agent29Raw36D110.b1Child ⟨false,false,5⟩ := by rfl

theorem child05_cover :
    Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
      (BB6.Agent29Raw36D110Live8.child 5) := by
  rw [child05_identity]
  apply Cover.leaf
  intro m hm
  exact BB6.Agent29Raw36D110.kid05_bound m hm

theorem live6_from_live5
    (h : ∀ i ∈ liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i)) :
    ∀ i ∈ BB6.Agent29Raw36D110Live6.liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i) := by
  intro i hi
  simp only [BB6.Agent29Raw36D110Live6.liveCodes,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact child05_cover
  · exact h 11 (by decide)
  · exact h 12 (by decide)
  · exact h 16 (by decide)
  · exact h 17 (by decide)
  · exact h 23 (by decide)

theorem parent_cover_from_live5
    (h : ∀ i ∈ liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i)) :
    Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
      BB6.Agent29Raw36D110Live8.parent :=
  BB6.Agent29Raw36D110Live6.parent_cover_from_live6
    (live6_from_live5 h)

theorem live5_count : liveCodes.length = 5 := by decide

#print axioms child05_identity
#print axioms child05_cover
#print axioms live6_from_live5
#print axioms parent_cover_from_live5
#print axioms live5_count
end BB6.Agent29Raw36D110Live5

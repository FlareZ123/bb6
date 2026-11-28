import Raw36D110Live5AfterE0LE1LB0LF
import Raw36D110Kid11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Consume the complete E0=0RF child of the D1=0RE branch after E0=0LE,
E0=1LB and E0=0LF.  The E0=0RF child is source-generated from six
inverse-stack NeverHalts witnesses and one exact finite-halting leaf.
The remaining four first-E0 Cover obligations are 1LA, 1LE, 1LF and 1RF.
-/

namespace BB6.Agent29Raw36D110Live4
open BB6Coverage BB6.Agent13BlankDelay

def liveCodes : List Nat := [12,16,17,23]

theorem child11_identity :
    BB6.Agent29Raw36D110Live8.child 11 =
      BB6.Agent29Raw36D110.b1Child ⟨false,true,5⟩ := by rfl

theorem child11_cover :
    Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
      (BB6.Agent29Raw36D110Live8.child 11) := by
  rw [child11_identity]
  apply Cover.leaf
  intro m hm
  exact BB6.Agent29Raw36D110.kid11_bound m hm

theorem live5_from_live4
    (h : ∀ i ∈ liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i)) :
    ∀ i ∈ BB6.Agent29Raw36D110Live5.liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i) := by
  intro i hi
  simp only [BB6.Agent29Raw36D110Live5.liveCodes,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact child11_cover
  · exact h 12 (by decide)
  · exact h 16 (by decide)
  · exact h 17 (by decide)
  · exact h 23 (by decide)

theorem parent_cover_from_live4
    (h : ∀ i ∈ liveCodes,
      Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
        (BB6.Agent29Raw36D110Live8.child i)) :
    Cover (WeightedBound BB6.Agent29Raw36D110Live8.B)
      BB6.Agent29Raw36D110Live8.parent :=
  BB6.Agent29Raw36D110Live5.parent_cover_from_live5
    (live5_from_live4 h)

theorem live4_count : liveCodes.length = 4 := by decide

#print axioms child11_identity
#print axioms child11_cover
#print axioms live5_from_live4
#print axioms parent_cover_from_live4
#print axioms live4_count
end BB6.Agent29Raw36D110Live4

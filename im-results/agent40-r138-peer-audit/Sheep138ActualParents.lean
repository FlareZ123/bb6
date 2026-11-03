import Sheep138ExactParents
import SheepGenericConverse

namespace Sheep138ActualParents

/-- For every k, two exact distinct predecessors have genuine source-level
Sheep.EvenEdge witnesses, with no blank-reachability claim. -/
theorem two_source_parents (k : Nat) :
    ∃ x1 x2 : Nat,
      x1 ≠ x2 ∧
      SheepEven.EvenEdge x1 (2^(138+4860*k)) ∧
      SheepEven.EvenEdge x2 (2^(138+4860*k)) ∧
      15*x1+2=2^(141+4860*k) ∧
      81*x2+68=2^(143+4860*k) := by
  obtain ⟨x1,x2,hneq,hg1,hg2,h1,h2⟩ := Sheep138ExactParents.two_generic_parents k
  exact ⟨x1,x2,hneq,
    SheepGenericConverse.generic_to_source hg1,
    SheepGenericConverse.generic_to_source hg2,h1,h2⟩

#print axioms two_source_parents
end Sheep138ActualParents

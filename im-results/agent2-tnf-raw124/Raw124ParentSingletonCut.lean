import Raw124ParentNestedCut
import Raw124B0REData

namespace BB6.Agent2Raw124ParentSingletonCut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent2Raw124ParentPartialCut BB6.Agent2Raw124ParentNestedCut

theorem child0RE_eq :
    child0RE = BB6.Agent2Raw124B0RE.pBranch :=
  tableOK_sound _ _ (by decide)

theorem cover0RE : Cover (WeightedBound parentBound) child0RE := by
  apply Cover.leaf
  intro m hm
  exact BB6.Agent12Raw124ZeroLFParent.weighted_mono (by decide : 2473 ≤ parentBound)
    (BB6.Agent2Raw124B0RE.bound_all m (child0RE_eq ▸ hm))

/-- The last remaining cylinder is exactly F1=0LF/F0=1RC. -/
theorem cover_of_last
    (hRC : Cover (WeightedBound parentBound) p0LF1RC) :
    Cover (WeightedBound parentBound) BB6.Agent32Raw124ParentJoin.parent124 :=
  cover_of_nested_two cover0RE hRC

#print axioms child0RE_eq
#print axioms cover0RE
#print axioms cover_of_last
end BB6.Agent2Raw124ParentSingletonCut

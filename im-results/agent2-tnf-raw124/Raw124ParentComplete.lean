import Raw124ParentSingletonCut
import Agent12RCFinal

namespace BB6.Agent2Raw124ParentComplete
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent2Raw124ParentPartialCut BB6.Agent2Raw124ParentNestedCut

theorem p0LF1RC_eq :
    p0LF1RC = BB6.Agent12Raw124ZeroLF1RC.pChild :=
  tableOK_sound _ _ (by decide)

theorem coverRC : Cover (WeightedBound parentBound) p0LF1RC := by
  apply Cover.leaf
  intro m hm
  exact BB6.Agent12Raw124ZeroLFParent.weighted_mono
    (by decide : 108667 ≤ parentBound)
    (BB6.Agent12Raw124ZeroLF1RC.bound_all m (p0LF1RC_eq ▸ hm))

theorem parent_cover :
    Cover (WeightedBound parentBound) BB6.Agent32Raw124ParentJoin.parent124 :=
  BB6.Agent2Raw124ParentSingletonCut.cover_of_last coverRC

#print axioms p0LF1RC_eq
#print axioms coverRC
#print axioms parent_cover
end BB6.Agent2Raw124ParentComplete

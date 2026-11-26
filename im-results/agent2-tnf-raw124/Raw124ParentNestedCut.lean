import Raw124ParentPartialCut
import Raw124ZeroLFParentFrontier

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent2Raw124ParentNestedCut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent2Raw124ParentPartialCut

abbrev p0LF1RC : PartialMachine :=
  BB6.Agent12Raw124ZeroLFParent.child ⟨true,true,2⟩

theorem p0LF_eq :
    child0LF = BB6.Agent12Raw124ZeroLFParent.parent :=
  tableOK_sound _ _ (by decide)

/-- The parent is now conditional only on F1=0RE and the precise
    nested F1=0LF, F0=1RC subcylinder. -/
theorem cover_of_nested_two
    (hRE : Cover (WeightedBound parentBound) child0RE)
    (hRC : Cover (WeightedBound parentBound) p0LF1RC) :
    Cover (WeightedBound parentBound) BB6.Agent32Raw124ParentJoin.parent124 := by
  apply cover_of_two
  · exact hRE.sound
  · intro m hm
    have hmp : compatible BB6.Agent12Raw124ZeroLFParent.parent m := p0LF_eq ▸ hm
    rcases BB6.Agent2Raw124ZeroLFParentFrontier.parent_cut m hmp with h | ⟨mv,hmv,hc⟩
    · exact BB6.Agent12Raw124ZeroLFParent.weighted_mono (by decide : 2931 ≤ parentBound) h
    · have he : mv = (⟨true,true,2⟩ : Move) := by
        simpa [BB6.Agent2Raw124ZeroLFParentFrontier.residualMoves] using hmv
      subst mv
      exact hRC.sound m hc

#print axioms p0LF_eq
#print axioms cover_of_nested_two
end BB6.Agent2Raw124ParentNestedCut

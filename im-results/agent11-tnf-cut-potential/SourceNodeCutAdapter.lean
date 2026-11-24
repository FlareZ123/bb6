import Enumerate62Adapter
import CutSensitivePotential

namespace BB6.Agent11CutPotential

open BB6.Agent5Enumerate62
open BB6.Agent48Queue

/-- Project an exact source-adapter node to the (holes, least-fresh-state)
    abstraction used by the cut-sensitive queue potential. -/
def sourceNodeAsCutNode (x : SourceNode) : Node :=
  ⟨x.holes.length, ⟨x.fresh % 7, Nat.mod_lt _ (by decide)⟩⟩

theorem sourceNodeAsCutNode_holes (x : SourceNode) :
    (sourceNodeAsCutNode x).holes = x.holes.length := rfl

theorem sourceNodeAsCutNode_cut (x : SourceNode) (hwf : SourceWF x) :
    (sourceNodeAsCutNode x).cut.val = x.fresh := by
  have hf : x.fresh < 7 := by
    have h := hwf.2.2.1
    omega
  simp [sourceNodeAsCutNode, Nat.mod_eq_of_lt hf]

theorem cutNodeWeight_sourceNode (x : SourceNode) (hwf : SourceWF x) :
    cutNodeWeight (sourceNodeAsCutNode x) =
      cutWeight x.fresh x.holes.length := by
  simp [cutNodeWeight, sourceNodeAsCutNode_cut x hwf,
    sourceNodeAsCutNode_holes x]

/-- Every source child projects to the existing-label or least-fresh child
    in the exact finite-state expansion model. -/
theorem sourceChildAsCutNode (x : SourceNode) (slot : BB6Coverage.Slot)
    (mv : BB6Coverage.Move) (hwf : SourceWF x) (hhole : x.tm slot = none)
    (hslot : slot.1.val < x.fresh) (hdest : mv.next.val ≤ x.fresh) :
    sourceNodeAsCutNode (sourceChild x slot mv) =
      if mv.next.val < x.fresh then
        existingChild (sourceNodeAsCutNode x)
      else
        freshChild (sourceNodeAsCutNode x) := by
  by_cases hlt : mv.next.val < x.fresh
  · have hne : mv.next.val ≠ x.fresh := by omega
    have hf : x.fresh < 7 := by
      have h := hwf.2.2.1
      omega
    simp only [if_pos hlt, existingChild, sourceNodeAsCutNode]
    apply (Node.mk.injEq).2
    constructor
    · simp [sourceChild_holes_length x slot mv hwf hhole]
    · simp [sourceChild, sourceChildFresh, hne, Nat.mod_eq_of_lt hf]
  · have heq : mv.next.val = x.fresh := by omega
    have hfresh : x.fresh < 6 := by omega
    simp only [if_neg hlt, freshChild, sourceNodeAsCutNode]
    apply (Node.mk.injEq).2
    constructor
    · simp [sourceChild_holes_length x slot mv hwf hhole]
    · simp [sourceChild, sourceChildFresh, heq,
        Nat.mod_eq_of_lt (by omega : x.fresh < 7),
        Nat.mod_eq_of_lt (by omega : x.fresh + 1 < 7)]

theorem cutNodeWeight_sourceChild (x : SourceNode) (slot : BB6Coverage.Slot)
    (mv : BB6Coverage.Move) (hwf : SourceWF x) (hhole : x.tm slot = none)
    (hslot : slot.1.val < x.fresh) (hdest : mv.next.val ≤ x.fresh) :
    cutNodeWeight (sourceNodeAsCutNode (sourceChild x slot mv)) =
      if mv.next.val < x.fresh then
        cutWeight x.fresh (x.holes.length - 1)
      else
        cutWeight (x.fresh + 1) (x.holes.length - 1) := by
  rw [sourceChildAsCutNode x slot mv hwf hhole hslot hdest]
  by_cases hlt : mv.next.val < x.fresh
  · simp [hlt, cutNodeWeight_existing,
      sourceNodeAsCutNode_cut x hwf, sourceNodeAsCutNode_holes x]
  · have heq : mv.next.val = x.fresh := by omega
    have hfresh : x.fresh < 6 := by omega
    have hcut : (sourceNodeAsCutNode x).cut.val < 6 := by
      simpa [sourceNodeAsCutNode_cut x hwf] using hfresh
    simp [heq, cutNodeWeight_fresh (sourceNodeAsCutNode x) hcut,
      sourceNodeAsCutNode_cut x hwf, sourceNodeAsCutNode_holes x]

#print axioms sourceNodeAsCutNode_cut
#print axioms cutNodeWeight_sourceNode
#print axioms sourceChildAsCutNode
#print axioms cutNodeWeight_sourceChild

end BB6.Agent11CutPotential

import Enumerate62Adapter
import CutSensitivePotential

namespace BB6.Agent11CutPotential

open BB6.Agent5Enumerate62
open BB6.Agent48Queue

/-- Project the exact source-adapter node record to the (holes, least-fresh
    state) abstraction used by the cut-sensitive queue potential. -/
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
  simp [cutNodeWeight, sourceNodeAsCutNode_cut x hwf]

/-- A source child projects to exactly the existing-label or least-fresh
    child in Agent 48's expansion model. This is the key field-level bridge
    needed to compute the potential directly from packed source nodes. -/
theorem sourceChildAsCutNode (x : SourceNode) (slot : Slot) (mv : Move)
    (hwf : SourceWF x) (hhole : x.tm slot = none)
    (hslot : slot.1.val < x.fresh) (hdest : mv.next.val ≤ x.fresh) :
    sourceNodeAsCutNode (sourceChild x slot mv) =
      if mv.next.val < x.fresh then
        existingChild (sourceNodeAsCutNode x)
      else
        freshChild (sourceNodeAsCutNode x) := by
  ext
  · simp [sourceNodeAsCutNode, sourceChild_holes_length x slot mv hwf hhole,
      existingChild, freshChild]
  · have hf : x.fresh < 7 := by
      have h := hwf.2.2.1
      omega
    have hcut := sourceNodeAsCutNode_cut x hwf
    by_cases heq : mv.next.val = x.fresh
    · have hfresh : x.fresh < 6 := by omega
      simp [sourceNodeAsCutNode, sourceChild, sourceChildFresh, heq,
        existingChild, freshChild, hcut, Nat.mod_eq_of_lt (by omega)]
    · have hlt : mv.next.val < x.fresh := by omega
      simp [sourceNodeAsCutNode, sourceChild, sourceChildFresh, heq, hlt,
        existingChild, freshChild, hcut, Nat.mod_eq_of_lt hf]

theorem cutNodeWeight_sourceChild (x : SourceNode) (slot : Slot) (mv : Move)
    (hwf : SourceWF x) (hhole : x.tm slot = none)
    (hslot : slot.1.val < x.fresh) (hdest : mv.next.val ≤ x.fresh) :
    cutNodeWeight (sourceNodeAsCutNode (sourceChild x slot mv)) =
      if mv.next.val < x.fresh then
        cutWeight x.fresh (x.holes.length - 1)
      else
        cutWeight (x.fresh + 1) (x.holes.length - 1) := by
  rw [sourceChildAsCutNode x slot mv hwf hhole hslot hdest]
  by_cases h : mv.next.val < x.fresh
  · simp [h, cutNodeWeight_existing]
  · have heq : mv.next.val = x.fresh := by omega
    simp [h, heq, cutNodeWeight_fresh, freshChild_cut]

#print axioms sourceNodeAsCutNode_cut
#print axioms cutNodeWeight_sourceNode
#print axioms sourceChildAsCutNode
#print axioms cutNodeWeight_sourceChild

end BB6.Agent11CutPotential

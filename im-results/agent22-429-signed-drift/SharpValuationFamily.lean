import ValuationEdges
import SharpEdgeFamily

namespace ValuationPacking

private def toSharpEdge {K : Nat} (e : Edge K) : SharpEdgeFamily.Edge K where
  v := e.v
  j := e.j
  next := e.next
  vpos := e.vpos
  vsmall := e.vsmall
  jpos := e.jpos
  eqn := e.eqn

private def sharpEdges {K : Nat} (es : List (Edge K)) : List (SharpEdgeFamily.Edge K) :=
  es.map toSharpEdge

private theorem sharpEdges_v_nodup {K : Nat} (es : List (Edge K))
    (hn : (es.map (fun e => e.v)).Nodup) :
    ((sharpEdges es).map (fun e => e.v)).Nodup := by
  unfold sharpEdges
  rw [List.map_map]
  change (es.map (fun e : Edge K => e.v)).Nodup
  exact hn

private theorem sharpEdges_j_sum {K : Nat} (es : List (Edge K)) :
    ((sharpEdges es).map (fun e => e.j)).sum =
      (es.map (fun e => e.j)).sum := by
  unfold sharpEdges
  rw [List.map_map]
  change (es.map (fun e : Edge K => e.j)).sum = _
  rfl

/-- Exact per-K four-adic capacity for the repository's existing Edge type. -/
theorem exact_edge_family_capacity (K : Nat) (es : List (Edge K))
    (hK : 0<K) (hn : (es.map (fun e => e.v)).Nodup) :
    (es.map (fun e => e.j)).sum ≤
      SharpPackingUniversal.F ((K-1)/3)-SharpPackingUniversal.F (K/4) := by
  have h := SharpEdgeFamily.edge_family_capacity K (sharpEdges es) hK
    (sharpEdges_v_nodup es hn)
  rw [sharpEdges_j_sum] at h
  exact h

theorem sharp_edge_family_budget (K : Nat) (es : List (Edge K))
    (hK : 15≤K) (hn : (es.map (fun e => e.v)).Nodup) :
    15*(es.map (fun e => e.j)).sum ≤ 2*K := by
  have h := SharpEdgeFamily.sharp_edge_family_budget K (sharpEdges es) hK
    (sharpEdges_v_nodup es hn)
  rw [sharpEdges_j_sum] at h
  exact h

#print axioms exact_edge_family_capacity
#print axioms sharp_edge_family_budget
end ValuationPacking

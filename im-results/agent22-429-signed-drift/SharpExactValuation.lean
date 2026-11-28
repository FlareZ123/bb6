import SharpExactConstruction
import SharpValuationFamily

namespace ValuationPacking
open SharpPackingUniversal

def fromSharpEdge {K : Nat} (e : SharpEdgeFamily.Edge K) : Edge K where
  v := e.v
  j := e.j
  next := e.next
  vpos := e.vpos
  vsmall := e.vsmall
  jpos := e.jpos
  eqn := e.eqn

def exactMaxEdges (K : Nat) : List (Edge K) :=
  (SharpExactConstruction.maxEdges K).map fromSharpEdge

theorem exactMaxEdges_v_nodup (K : Nat) :
    ((exactMaxEdges K).map (fun e => e.v)).Nodup := by
  unfold exactMaxEdges
  rw [List.map_map]
  change ((SharpExactConstruction.maxEdges K).map (fun e => e.v)).Nodup
  exact SharpExactConstruction.maxEdges_sources_nodup K

theorem exactMaxEdges_j_sum (K : Nat) :
    ((exactMaxEdges K).map (fun e => e.j)).sum =
      F ((K-1)/3)-F (K/4) := by
  unfold exactMaxEdges
  rw [List.map_map]
  change ((SharpExactConstruction.maxEdges K).map (fun e => e.j)).sum = _
  exact SharpExactConstruction.maxEdges_weight K

/-- Exact extremal characterization in the repository's canonical Edge type:
    for every positive K the four-adic formula is both a universal upper bound
    and is attained by an explicit legal distinct-source family. -/
theorem exact_capacity_characterization (K : Nat) (hK : 0<K) :
    (∀ es : List (Edge K), (es.map (fun e => e.v)).Nodup →
      (es.map (fun e => e.j)).sum ≤ F ((K-1)/3)-F (K/4)) ∧
    (∃ es : List (Edge K), (es.map (fun e => e.v)).Nodup ∧
      (es.map (fun e => e.j)).sum = F ((K-1)/3)-F (K/4)) := by
  constructor
  · intro es hn
    exact exact_edge_family_capacity K es hK hn
  · exact ⟨exactMaxEdges K, exactMaxEdges_v_nodup K, exactMaxEdges_j_sum K⟩

#print axioms exact_capacity_characterization
end ValuationPacking

import ValuationPrimitive
import SharpValuationFamily

namespace ValuationPacking

private theorem nodup_map_inj_sharp {α β : Type} (f : α → β)
    (hinj : Function.Injective f) {l : List α} (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot,ht⟩ := List.nodup_cons.mp h
    simp only [List.map_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
      exact hnot ((hinj he.symm) ▸ hy)
    · exact ih ht

theorem windowEdges_v_nodup_sharp (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (hprim : BackwardPrimitive n j) :
    ((windowEdges (n:=n) v j h).map (fun e => e.v)).Nodup := by
  unfold windowEdges
  rw [List.map_map]
  change ((List.finRange n).map (fun s : Fin n => v (s.val:Int))).Nodup
  exact nodup_map_inj_sharp (fun s : Fin n => v (s.val:Int))
    (window_source_injective K n v j h hprim) (List.nodup_finRange n)

theorem windowEdges_j_sum_sharp (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1))) :
    ((windowEdges (n:=n) v j h).map (fun e => e.j)).sum =
      ((List.finRange n).map (fun s : Fin n => j (s.val:Int))).sum := by
  unfold windowEdges
  rw [List.map_map]
  rfl

/-- Exact per-K capacity for every backward-primitive valuation window. -/
theorem primitive_window_exact_capacity (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (hprim : BackwardPrimitive n j) (hK : 0<K) :
    ((List.finRange n).map (fun s : Fin n => j (s.val:Int))).sum ≤
      SharpPackingUniversal.F ((K-1)/3)-SharpPackingUniversal.F (K/4) := by
  let es := windowEdges (n:=n) v j h
  have hn : (es.map (fun e => e.v)).Nodup :=
    windowEdges_v_nodup_sharp K n v j h hprim
  have hb := exact_edge_family_capacity K es hK hn
  have hs := windowEdges_j_sum_sharp K n v j h
  rwa [hs] at hb

/-- Sharp replacement for the old 6J<K primitive-window obstruction. -/
theorem no_primitive_window_sharp (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (hprim : BackwardPrimitive n j)
    (hK : 15 ≤ K)
    (hgap : 2*K < 15 * ((List.finRange n).map
      (fun s : Fin n => j (s.val:Int))).sum) : False := by
  let es := windowEdges (n:=n) v j h
  have hn : (es.map (fun e => e.v)).Nodup :=
    windowEdges_v_nodup_sharp K n v j h hprim
  have hb := sharp_edge_family_budget K es hK hn
  have hs := windowEdges_j_sum_sharp K n v j h
  rw [hs] at hb
  omega

#print axioms primitive_window_exact_capacity
#print axioms windowEdges_v_nodup_sharp
#print axioms no_primitive_window_sharp
end ValuationPacking

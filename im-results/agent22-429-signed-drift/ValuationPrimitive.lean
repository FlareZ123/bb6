import ValuationEdges

namespace ValuationPacking

theorem backwards_unique (K : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (a b : Int) (hab : v a = v b) :
    ∀ k : Nat, v (a-(k:Int)) = v (b-(k:Int)) ∧
       (0 < k → j (a-(k:Int)) = j (b-(k:Int))) := by
  intro k
  induction k with
  | zero =>
    constructor
    · simpa using hab
    · intro hk
      omega
  | succ k ih =>
    let a0 : Int := a - ((k+1:Nat):Int)
    let b0 : Int := b - ((k+1:Nat):Int)
    have ha : a0 + 1 = a-(k:Int) := by dsimp [a0]; omega
    have hb : b0 + 1 = b-(k:Int) := by dsimp [b0]; omega
    have heq : v (a0+1) = v (b0+1) := by rw [ha,hb]; exact ih.1
    have hA := h a0
    have hB := h b0
    rw [← heq] at hB
    have hinj := quotient_injective K (v a0) (v b0) (j a0) (j b0)
      (v (a0+1)) hA hB
    constructor
    · simpa only [a0,b0] using hinj.1
    · intro _
      simpa only [a0,b0] using hinj.2

def BackwardPrimitive (n : Nat) (j : Int → Nat) : Prop :=
  ∀ a b : Nat, a < b → b < n →
    ∃ k : Nat, 0 < k ∧ k ≤ n ∧
      j ((a:Int)-(k:Int)) ≠ j ((b:Int)-(k:Int))

theorem window_source_injective (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (hprim : BackwardPrimitive n j) :
    Function.Injective (fun s : Fin n => v (s.val:Int)) := by
  intro x y hxy
  by_cases hEq : x = y
  · exact hEq
  have hvals : x.val ≠ y.val := by
    intro he
    exact hEq (Fin.ext he)
  have hcase : x.val < y.val ∨ y.val < x.val := by omega
  rcases hcase with hlt | hlt
  · obtain ⟨k,hkpos,hkle,hne⟩ := hprim x.val y.val hlt y.isLt
    have he := (backwards_unique K v j h (x.val:Int) (y.val:Int) hxy k).2 hkpos
    exact False.elim (hne he)
  · obtain ⟨k,hkpos,hkle,hne⟩ := hprim y.val x.val hlt x.isLt
    have he := (backwards_unique K v j h (y.val:Int) (x.val:Int) hxy.symm k).2 hkpos
    exact False.elim (hne he)

private theorem nodup_map_inj {α β : Type} (f : α → β)
    (hinj : Function.Injective f) {l : List α} (h : l.Nodup) :
    (l.map f).Nodup := by
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

private def windowEdge {K n : Nat} (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (s : Fin n) : Edge K where
  v := v (s.val:Int)
  j := j (s.val:Int)
  next := v ((s.val:Int)+1)
  vpos := (h (s.val:Int)).1
  vsmall := (h (s.val:Int)).2.1
  jpos := (h (s.val:Int)).2.2.1
  eqn := (h (s.val:Int)).2.2.2

def windowEdges {K n : Nat} (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1))) :
    List (Edge K) :=
  (List.finRange n).map (windowEdge v j h)

theorem no_primitive_window (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (hprim : BackwardPrimitive n j)
    (hpos : 0 < ((List.finRange n).map (fun s : Fin n => j (s.val:Int))).sum)
    (hK : K ≤ 6 * ((List.finRange n).map (fun s : Fin n => j (s.val:Int))).sum) : False := by
  let es := windowEdges (n:=n) v j h
  have hnodup : (es.map (fun e => e.v)).Nodup := by
    change ((List.finRange n).map (windowEdge v j h)).map (fun e => e.v) |>.Nodup
    rw [List.map_map]
    change ((List.finRange n).map (fun s : Fin n => v (s.val:Int))).Nodup
    exact nodup_map_inj (fun s : Fin n => v (s.val:Int))
      (window_source_injective K n v j h hprim) (List.nodup_finRange n)
  have hsum : (es.map (fun e => e.j)).sum =
      ((List.finRange n).map (fun s : Fin n => j (s.val:Int))).sum := by
    change (((List.finRange n).map (windowEdge v j h)).map (fun e => e.j)).sum = _
    rw [List.map_map]
    rfl
  exact no_distinct_edge_budget K es hnodup (by rwa [hsum]) (by rwa [hsum])

#print axioms no_primitive_window
#print axioms window_source_injective
#print axioms backwards_unique
end ValuationPacking

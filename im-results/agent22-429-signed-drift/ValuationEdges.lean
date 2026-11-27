import ValuationPacking

namespace ValuationPacking

structure Edge (K : Nat) where
  v : Nat
  j : Nat
  next : Nat
  vpos : 0 < v
  vsmall : 3*v < K
  jpos : 0 < j
  eqn : 4^j * next = v+K

def atLevel {K : Nat} (e : Edge K) (s : Fin e.j) : Point K where
  v := e.v
  k := s.val+1
  z := 4^(e.j-(s.val+1)) * e.next
  witness := by
    dsimp [Witness]
    refine ⟨e.vpos, e.vsmall, by omega, ?_⟩
    have hl : s.val+1 ≤ e.j := by omega
    have hr := Nat.add_sub_of_le hl
    calc
      4 ^ (s.val+1) * (4 ^ (e.j-(s.val+1)) * e.next)
        = (4 ^ (s.val+1) * 4 ^ (e.j-(s.val+1))) * e.next := by simp only [Nat.mul_assoc]
      _ = 4^((s.val+1)+(e.j-(s.val+1))) * e.next := by exact congrArg (fun n : Nat => n * e.next) (Nat.pow_add 4 (s.val+1) (e.j-(s.val+1))).symm
      _ = 4 ^ e.j * e.next := by rw [hr]
      _ = e.v+K := e.eqn

def levels {K : Nat} (e : Edge K) : List (Point K) :=
  (List.finRange e.j).map (atLevel e)

theorem levels_length {K : Nat} (e : Edge K) : (levels e).length = e.j := by
  simp [levels]

private theorem nodup_map_inj {α β : Type} (f : α → β)
    (hinj : Function.Injective f) {l : List α} (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot,hxs⟩ := List.nodup_cons.mp h
    simp only [List.map_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      obtain ⟨y,hy,hxy⟩ := List.mem_map.mp hmem
      have hEq : x=y := hinj hxy.symm
      exact hnot (hEq ▸ hy)
    · exact ih hxs

theorem levels_pair_nodup {K : Nat} (e : Edge K) :
    ((levels e).map (fun p => (p.v,p.k))).Nodup := by
  unfold levels
  simp only [List.map_map]
  let f : Fin e.j → Nat × Nat := fun s => (e.v, s.val+1)
  change (List.map f (List.finRange e.j)).Nodup
  apply nodup_map_inj f
  · intro a b h
    exact Fin.ext (by have hh := congrArg Prod.snd h; simp [f] at hh; omega)
  · exact List.nodup_finRange e.j

def allLevels {K : Nat} (es : List (Edge K)) : List (Point K) :=
  es.flatMap levels

theorem levels_sources {K : Nat} (e : Edge K) {p : Point K}
    (h : p ∈ levels e) : p.v = e.v := by
  unfold levels at h
  obtain ⟨f,hf,hfp⟩ := List.mem_map.mp h
  rw [← hfp]
  rfl

theorem allLevels_sources {K : Nat} (es : List (Edge K)) {p : Point K}
    (h : p ∈ allLevels es) :
    ∃ e ∈ es, p.v = e.v := by
  unfold allLevels at h
  obtain ⟨e,he,hpe⟩ := List.mem_flatMap.mp h
  exact ⟨e, he, levels_sources e hpe⟩

theorem allLevels_pair_nodup {K : Nat} (es : List (Edge K))
    (h : (es.map (fun e => e.v)).Nodup) :
    ((allLevels es).map (fun p => (p.v,p.k))).Nodup := by
  induction es with
  | nil => simp [allLevels]
  | cons e es ih =>
    simp only [List.map_cons] at h
    obtain ⟨hnot,hrest⟩ := List.nodup_cons.mp h
    have htail := ih hrest
    change (((levels e) ++ (allLevels es)).map (fun p => (p.v,p.k))).Nodup
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨levels_pair_nodup e, htail, ?_⟩
    intro a ha b hb hEq
    obtain ⟨p,hp,hap⟩ := List.mem_map.mp ha
    obtain ⟨q,hq,hbq⟩ := List.mem_map.mp hb
    have hpv := levels_sources e hp
    obtain ⟨e', he', hqv⟩ := allLevels_sources es hq
    have hfirst : p.v = q.v := by
      have aa := congrArg Prod.fst hEq
      simp only [← hap, ← hbq] at aa
      exact aa
    apply hnot
    exact List.mem_map.mpr ⟨e', he', by omega⟩

theorem allLevels_length {K : Nat} (es : List (Edge K)) :
    (allLevels es).length = (es.map (fun e => e.j)).sum := by
  induction es with
  | nil => simp [allLevels]
  | cons e es ih =>
    change (levels e ++ allLevels es).length = e.j + (es.map (fun e => e.j)).sum
    simp [levels_length e, ih]

theorem edge_family_budget (K : Nat) (es : List (Edge K))
    (h : (es.map (fun e => e.v)).Nodup) :
    (es.map (fun e => e.j)).sum ≤ (K-1)/6 := by
  have hpack := finite_valuation_packing_pairs K (allLevels es)
    (allLevels_pair_nodup es h)
  rwa [allLevels_length es] at hpack

theorem equal_successor_forces_equal_parameters {K : Nat} (e f : Edge K)
    (h : e.next = f.next) : e.v = f.v ∧ e.j = f.j := by
  exact quotient_injective K e.v f.v e.j f.j e.next
    ⟨e.vpos,e.vsmall,e.jpos,e.eqn⟩
    (by simpa [h] using (show Witness K f.v f.j f.next from
      ⟨f.vpos,f.vsmall,f.jpos,f.eqn⟩))

theorem no_distinct_edge_budget (K : Nat) (es : List (Edge K))
    (h : (es.map (fun e => e.v)).Nodup)
    (hpos : 0 < (es.map (fun e => e.j)).sum)
    (hK : K ≤ 6*(es.map (fun e => e.j)).sum) : False := by
  have hb := edge_family_budget K es h
  omega

#print axioms equal_successor_forces_equal_parameters
#print axioms no_distinct_edge_budget
#print axioms edge_family_budget
#print axioms levels_pair_nodup
end ValuationPacking

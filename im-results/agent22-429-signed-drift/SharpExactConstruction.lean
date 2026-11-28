import SharpEdgeFamily

namespace SharpExactConstruction
open SharpPackingUniversal
open SharpEdgeFamily

theorem pow_fourVal_dvd : ∀ z : Nat, 4^(fourVal z) ∣ z := by
  intro z
  induction z using Nat.strongRecOn with
  | ind z ih =>
    by_cases hz : z=0
    · subst z
      simp [fourVal]
    · by_cases hm : z%4=0
      · have hpos : 0<z := Nat.pos_of_ne_zero hz
        have hlt : z/4<z := by omega
        have hi := ih (z/4) hlt
        have h4 : 4∣z := Nat.dvd_of_mod_eq_zero hm
        have hzq : 4*(z/4)=z := Nat.mul_div_cancel' h4
        have hv : fourVal z=1+fourVal (z/4) := by
          rw [fourVal]
          simp [hz,hm]
        rw [hv]
        rw [show 4^(1+fourVal (z/4))=4*4^(fourVal (z/4)) by
          rw [Nat.add_comm, Nat.pow_succ]; ac_rfl]
        obtain ⟨q,hq⟩ := hi
        refine ⟨q,?_⟩
        calc
          z = 4*(z/4) := hzq.symm
          _ = 4*(4^(fourVal (z/4))*q) := congrArg (fun t => 4*t) hq
          _ = (4*4^(fourVal (z/4)))*q := by ac_rfl
      · have hv : fourVal z=0 := by
          rw [fourVal]
          simp [hz,hm]
        rw [hv]
        simp

def width (K : Nat) : Nat := (K-1)/3-K/4

def zAt (K : Nat) (i : Fin (width K)) : Nat := K/4+i.val+1

theorem zAt_lower (K : Nat) (i : Fin (width K)) : K/4<zAt K i := by
  unfold zAt
  omega

theorem zAt_upper (K : Nat) (i : Fin (width K)) : zAt K i≤(K-1)/3 := by
  unfold zAt width at *
  omega

theorem zAt_pos (K : Nat) (i : Fin (width K)) : 0<zAt K i := by
  have := zAt_lower K i
  omega

def maxEdge (K : Nat) (i : Fin (width K)) : Edge K where
  v := 4*zAt K i-K
  j := 1+fourVal (zAt K i)
  next := zAt K i / 4^(fourVal (zAt K i))
  vpos := by
    have hl := zAt_lower K i
    have hf : 4*(K/4)≤K := by omega
    have hgap : K<4*zAt K i := by omega
    omega
  vsmall := by
    have hu := zAt_upper K i
    have hi := i.isLt
    have hwidth : 0<width K := by omega
    have hK : 0<K := by unfold width at hwidth; omega
    have hfloor : 3*((K-1)/3)≤K-1 := by omega
    have hzle : 3*zAt K i≤3*((K-1)/3) := Nat.mul_le_mul_left 3 hu
    have hz : 3*zAt K i<K := by omega
    have hl := zAt_lower K i
    have hk : K<4*zAt K i := by omega
    omega
  jpos := by omega
  eqn := by
    have hd := pow_fourVal_dvd (zAt K i)
    have hmul : 4^(fourVal (zAt K i)) *
        (zAt K i / 4^(fourVal (zAt K i))) = zAt K i :=
      Nat.mul_div_cancel' hd
    have hp : 4^(1+fourVal (zAt K i)) =
        4*4^(fourVal (zAt K i)) := by
      rw [Nat.add_comm, Nat.pow_succ]
      ac_rfl
    rw [hp]
    rw [Nat.mul_assoc,hmul]
    have hl := zAt_lower K i
    have hk : K<4*zAt K i := by omega
    omega

def maxEdges (K : Nat) : List (Edge K) :=
  (List.finRange (width K)).map (maxEdge K)

private theorem nodup_map_inj {α β : Type} (f : α → β)
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

theorem maxEdge_source_injective (K : Nat) :
    Function.Injective (fun i : Fin (width K) => (maxEdge K i).v) := by
  intro a b h
  apply Fin.ext
  change 4*zAt K a-K=4*zAt K b-K at h
  have hla := zAt_lower K a
  have hlb := zAt_lower K b
  unfold zAt at h
  omega

theorem maxEdges_sources_nodup (K : Nat) :
    ((maxEdges K).map (fun e => e.v)).Nodup := by
  unfold maxEdges
  rw [List.map_map]
  exact nodup_map_inj (fun i : Fin (width K) => (maxEdge K i).v)
    (maxEdge_source_injective K) (List.nodup_finRange (width K))

theorem interval_weight (a n : Nat) :
    ((List.finRange n).map (fun i : Fin n => 1+fourVal (a+i.val+1))).sum + F a =
      F (a+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ_last]
      rw [List.map_append, List.sum_append]
      simp only [List.map_map, List.map_singleton, List.sum_cons, List.sum_nil, Nat.add_zero]
      have hmap : (List.finRange n).map
          ((fun i : Fin (n+1) => 1+fourVal (a+i.val+1)) ∘ Fin.castSucc) =
          (List.finRange n).map (fun i : Fin n => 1+fourVal (a+i.val+1)) := by
        apply List.map_congr_left
        intro i hi
        rfl
      rw [hmap]
      have hj := F_jump (a+n+1) (by omega)
      have hs : a+n+1-1=a+n := by omega
      rw [hs] at hj
      simp only [Fin.val_last]
      have hadd : a+(n+1)=a+n+1 := by omega
      rw [hadd]
      omega

theorem maxEdges_weight_plus_F (K : Nat) :
    ((maxEdges K).map (fun e => e.j)).sum + F (K/4) =
      F ((K-1)/3) := by
  unfold maxEdges
  rw [List.map_map]
  change ((List.finRange (width K)).map
    (fun i : Fin (width K) => 1+fourVal (K/4+i.val+1))).sum + F (K/4) = _
  have h := interval_weight (K/4) (width K)
  have hab : K/4≤(K-1)/3 := by omega
  have hw : K/4+width K=(K-1)/3 := by
    unfold width
    omega
  rw [hw] at h
  exact h

theorem maxEdges_weight (K : Nat) :
    ((maxEdges K).map (fun e => e.j)).sum =
      F ((K-1)/3)-F (K/4) := by
  have h := maxEdges_weight_plus_F K
  omega

/-- Exact capacity is attained by an explicit family for every K. -/
theorem exact_capacity_attained (K : Nat) :
    ∃ es : List (Edge K),
      (es.map (fun e => e.v)).Nodup ∧
      (es.map (fun e => e.j)).sum = F ((K-1)/3)-F (K/4) := by
  exact ⟨maxEdges K,maxEdges_sources_nodup K,maxEdges_weight K⟩

#print axioms pow_fourVal_dvd
#print axioms exact_capacity_attained
end SharpExactConstruction

import SharpPackingUniversal

namespace SharpEdgeFamily
open SharpPackingUniversal

structure Edge (K : Nat) where
  v : Nat
  j : Nat
  next : Nat
  vpos : 0 < v
  vsmall : 3*v < K
  jpos : 0 < j
  eqn : 4^j * next = v+K

def upperQuotient {K : Nat} (e : Edge K) : Nat :=
  4^(e.j-1)*e.next

theorem upperQuotient_eq {K : Nat} (e : Edge K) :
    4*upperQuotient e = e.v+K := by
  have hjpos := e.jpos
  have hj : e.j=e.j-1+1 := by omega
  have hp : 4^e.j=4*4^(e.j-1) := by
    calc
      4^e.j=4^((e.j-1)+1) := by rw [← hj]
      _=4^(e.j-1)*4 := by rw [Nat.pow_succ]
      _=4*4^(e.j-1) := by ac_rfl
  calc
    4*upperQuotient e = (4*4^(e.j-1))*e.next := by
      unfold upperQuotient
      ac_rfl
    _=4^e.j*e.next := by rw [←hp]
    _=e.v+K := e.eqn

theorem upperQuotient_interval {K : Nat} (e : Edge K) :
    K < 4*upperQuotient e ∧ 3*upperQuotient e < K := by
  have hh := upperQuotient_eq e
  have hpos := e.vpos
  have hsmall := e.vsmall
  omega

theorem upperQuotient_pos {K : Nat} (e : Edge K) : 0 < upperQuotient e := by
  by_cases hz : upperQuotient e = 0
  · have hi := (upperQuotient_interval e).1
    rw [hz] at hi
    simp at hi
  · exact Nat.pos_of_ne_zero hz

theorem upperQuotient_sources_injective {K : Nat}
    (e f : Edge K) (h : upperQuotient e=upperQuotient f) :
    e.v=f.v := by
  have he := upperQuotient_eq e
  have hf := upperQuotient_eq f
  rw [h] at he
  omega

theorem upperQuotient_level_divides {K : Nat} (e : Edge K) :
    4^(e.j-1) ∣ upperQuotient e := by
  exact ⟨e.next,rfl⟩

theorem fourVal_eq_of_mod_zero (n : Nat) (hn : 0<n) (hmod : n%4=0) :
    fourVal n = 1+fourVal (n/4) := by
  rw [fourVal]
  simp [Nat.ne_of_gt hn, hmod]

theorem fourVal_eq_zero_of_mod_ne (n : Nat) (hn : 0<n) (hmod : n%4≠0) :
    fourVal n = 0 := by
  rw [fourVal]
  simp [Nat.ne_of_gt hn, hmod]

theorem le_fourVal_of_pow_dvd : ∀ e n : Nat, 0<n → 4^e ∣ n → e ≤ fourVal n := by
  intro e
  induction e with
  | zero =>
      intro n hn hd
      simp
  | succ e ih =>
      intro n hn hd
      have hmul : 4 * 4^e ∣ n := by
        simpa [Nat.pow_succ, Nat.mul_comm] using hd
      have hbase : 4 ∣ 4 * 4^e := ⟨4^e, rfl⟩
      have h4div : 4 ∣ n := Nat.dvd_trans hbase hmul
      have hmod : n%4=0 := Nat.mod_eq_zero_of_dvd h4div
      have hfour : 4≤n := Nat.le_of_dvd hn h4div
      have hqpos : 0<n/4 := Nat.div_pos hfour (by omega)
      have hq : 4^e ∣ n/4 := Nat.dvd_div_of_mul_dvd hmul
      have hi := ih (n/4) hqpos hq
      rw [fourVal_eq_of_mod_zero n hn hmod]
      omega

theorem edge_level_le_val {K : Nat} (e : Edge K) :
    e.j ≤ 1 + fourVal (upperQuotient e) := by
  have hd := upperQuotient_level_divides e
  have hp := upperQuotient_pos e
  have hv := le_fourVal_of_pow_dvd (e.j-1) (upperQuotient e) hp hd
  have hj := e.jpos
  omega

def slotsFor (z : Nat) : List (Nat × Nat) :=
  (List.range (1 + fourVal z)).map (fun r => (z,r))

private theorem pair_second_injective (z : Nat) :
    Function.Injective (fun r : Nat => (z,r)) := by
  intro a b h
  exact congrArg Prod.snd h

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

theorem slotsFor_nodup (z : Nat) : (slotsFor z).Nodup := by
  unfold slotsFor
  exact nodup_map_inj (fun r : Nat => (z,r)) (pair_second_injective z)
    (show (List.range (1+fourVal z)).Nodup from List.nodup_range)

theorem mem_slotsFor (z r : Nat) :
    (z,r) ∈ slotsFor z ↔ r < 1+fourVal z := by
  unfold slotsFor
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := List.mem_map.mp h
    have hs := congrArg Prod.snd he
    have hqr := List.mem_range.mp hq
    omega
  · intro hr
    exact List.mem_map.mpr ⟨r,List.mem_range.mpr hr,rfl⟩

def slotsRange (a : Nat) : Nat → List (Nat × Nat)
| 0 => []
| n+1 => slotsRange a n ++ slotsFor (a+n+1)

theorem slotsRange_bound {a n z r : Nat}
    (h : (z,r) ∈ slotsRange a n) : a < z ∧ z ≤ a+n := by
  induction n with
  | zero => simp [slotsRange] at h
  | succ n ih =>
      simp only [slotsRange] at h
      have hm := List.mem_append.mp h
      rcases hm with hold | hnew
      · have hh := ih hold
        omega
      · have hz : z=a+n+1 := by
          unfold slotsFor at hnew
          obtain ⟨q,hq,he⟩ := List.mem_map.mp hnew
          exact (congrArg Prod.fst he).symm
        omega

theorem slotsRange_mem {a n z r : Nat}
    (ha : a<z) (hz : z≤a+n) (hr : r<1+fourVal z) :
    (z,r) ∈ slotsRange a n := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [slotsRange]
      apply List.mem_append.mpr
      by_cases hlast : z=a+n+1
      · right
        subst z
        exact (mem_slotsFor (a+n+1) r).2 hr
      · left
        apply ih
        omega

theorem slotsRange_nodup (a n : Nat) : (slotsRange a n).Nodup := by
  induction n with
  | zero => simp [slotsRange]
  | succ n ih =>
      simp only [slotsRange]
      apply List.nodup_append.mpr
      refine ⟨ih, slotsFor_nodup (a+n+1), ?_⟩
      intro p hp q hq heq
      have hpbd := slotsRange_bound hp
      have hqfst : q.1=a+n+1 := by
        unfold slotsFor at hq
        obtain ⟨r,hr,hre⟩ := List.mem_map.mp hq
        simpa [← hre]
      have hpq : p.1=q.1 := congrArg Prod.fst heq
      omega

theorem slotsRange_length_add_F (a n : Nat) :
    (slotsRange a n).length + F a = F (a+n) := by
  induction n with
  | zero => simp [slotsRange]
  | succ n ih =>
      simp only [slotsRange, List.length_append]
      have hlen : (slotsFor (a+n+1)).length = 1+fourVal (a+n+1) := by
        simp [slotsFor]
      rw [hlen]
      have hjump := F_jump (a+n+1) (by omega)
      have hs : a+n+1-1=a+n := by omega
      rw [hs] at hjump
      have hadd : a+(n+1)=a+n+1 := by omega
      rw [hadd]
      omega

#print axioms slotsRange_nodup
#print axioms slotsRange_length_add_F

def edgeSlots {K : Nat} (e : Edge K) : List (Nat × Nat) :=
  (List.range e.j).map (fun r => (upperQuotient e,r))

theorem edgeSlots_length {K : Nat} (e : Edge K) :
    (edgeSlots e).length=e.j := by simp [edgeSlots]

theorem edgeSlots_nodup {K : Nat} (e : Edge K) : (edgeSlots e).Nodup := by
  unfold edgeSlots
  exact nodup_map_inj (fun r : Nat => (upperQuotient e,r))
    (pair_second_injective (upperQuotient e))
    (show (List.range e.j).Nodup from List.nodup_range)

theorem edgeSlots_first {K : Nat} (e : Edge K) {p : Nat × Nat}
    (h : p∈edgeSlots e) : p.1=upperQuotient e := by
  unfold edgeSlots at h
  obtain ⟨r,hr,he⟩ := List.mem_map.mp h
  simpa [← he]

theorem edgeSlots_second_lt {K : Nat} (e : Edge K) {p : Nat × Nat}
    (h : p∈edgeSlots e) : p.2<e.j := by
  unfold edgeSlots at h
  obtain ⟨r,hr,he⟩ := List.mem_map.mp h
  have hh := List.mem_range.mp hr
  simpa [← he] using hh

def allEdgeSlots {K : Nat} (es : List (Edge K)) : List (Nat × Nat) :=
  es.flatMap edgeSlots

theorem allEdgeSlots_origin {K : Nat} (es : List (Edge K)) {p : Nat × Nat}
    (h : p∈allEdgeSlots es) : ∃ e∈es, p∈edgeSlots e := by
  unfold allEdgeSlots at h
  obtain ⟨e,he,hp⟩ := List.mem_flatMap.mp h
  exact ⟨e,he,hp⟩

theorem allEdgeSlots_length {K : Nat} (es : List (Edge K)) :
    (allEdgeSlots es).length=(es.map (fun e => e.j)).sum := by
  induction es with
  | nil => simp [allEdgeSlots]
  | cons e es ih =>
      change (edgeSlots e ++ allEdgeSlots es).length =
        e.j+(es.map (fun e => e.j)).sum
      simp [edgeSlots_length e,ih]

theorem allEdgeSlots_nodup {K : Nat} (es : List (Edge K))
    (h : (es.map (fun e => e.v)).Nodup) : (allEdgeSlots es).Nodup := by
  induction es with
  | nil => simp [allEdgeSlots]
  | cons e es ih =>
      simp only [List.map_cons] at h
      obtain ⟨hnot,hrest⟩ := List.nodup_cons.mp h
      have htail := ih hrest
      change (edgeSlots e ++ allEdgeSlots es).Nodup
      apply List.nodup_append.mpr
      refine ⟨edgeSlots_nodup e,htail,?_⟩
      intro p hp q hq heq
      have hpfirst := edgeSlots_first e hp
      obtain ⟨e',he',hqe'⟩ := allEdgeSlots_origin es hq
      have hqfirst := edgeSlots_first e' hqe'
      have hfirst : upperQuotient e=upperQuotient e' := by
        have hh := congrArg Prod.fst heq
        omega
      have hv : e.v=e'.v := upperQuotient_sources_injective e e' hfirst
      apply hnot
      exact List.mem_map.mpr ⟨e',he',hv.symm⟩

theorem allEdgeSlots_subset_capacity (K : Nat) (es : List (Edge K))
    (hK : 0<K) :
    allEdgeSlots es ⊆ slotsRange (K/4) (((K-1)/3)-(K/4)) := by
  rintro ⟨z,r⟩ hp
  obtain ⟨e,he,hpe⟩ := allEdgeSlots_origin es hp
  have hfirst0 := edgeSlots_first e hpe
  have hsecond0 := edgeSlots_second_lt e hpe
  have hfirst : z=upperQuotient e := by simpa using hfirst0
  have hsecond : r<e.j := by simpa using hsecond0
  subst z
  have hint := upperQuotient_interval e
  have hlevel := edge_level_le_val e
  have hab : K/4≤(K-1)/3 := by omega
  have hlow : K/4<upperQuotient e := by omega
  have hhigh : upperQuotient e≤(K-1)/3 := by omega
  have hsum : K/4 + (((K-1)/3)-(K/4)) = (K-1)/3 := by omega
  have hr : r<1+fourVal (upperQuotient e) := by omega
  apply slotsRange_mem hlow
  · rw [hsum]
    exact hhigh
  · exact hr

theorem edge_family_capacity (K : Nat) (es : List (Edge K))
    (hK : 0<K) (hn : (es.map (fun e => e.v)).Nodup) :
    (es.map (fun e => e.j)).sum ≤
      F ((K-1)/3)-F (K/4) := by
  have hnodup := allEdgeSlots_nodup es hn
  have hsub := allEdgeSlots_subset_capacity K es hK
  have hlen := List.Nodup.length_le_of_subset hnodup hsub
  rw [allEdgeSlots_length] at hlen
  have hab : K/4≤(K-1)/3 := by omega
  have hsum : K/4+(((K-1)/3)-(K/4))=(K-1)/3 := by omega
  have hcap := slotsRange_length_add_F (K/4) (((K-1)/3)-(K/4))
  rw [hsum] at hcap
  omega

theorem sharp_edge_family_budget (K : Nat) (es : List (Edge K))
    (hK : 15≤K) (hn : (es.map (fun e => e.v)).Nodup) :
    15*(es.map (fun e => e.j)).sum ≤ 2*K := by
  have hc := edge_family_capacity K es (by omega) hn
  have hm := Nat.mul_le_mul_left 15 hc
  exact Nat.le_trans hm (sharp_capacity K hK)

#print axioms edge_family_capacity
#print axioms sharp_edge_family_budget
#print axioms le_fourVal_of_pow_dvd
end SharpEdgeFamily

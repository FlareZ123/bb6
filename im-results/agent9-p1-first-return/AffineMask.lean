import AffineResidue
namespace BB6.Agent9AffineResidue
open BB6.P1CarryExtinction

def descend (k : Nat) : Nat → List Node → List Node
  | 0, ps => ps
  | d+1, ps => (descend k d ps).flatMap fun p => [advance (k+d) p false,advance (k+d) p true]

theorem descend_nodes (k d : Nat) (hk : 0<k) :
    descend k d (nodes (k-1))=nodes (k+d-1) := by
  induction d with
  | zero => simp [descend]
  | succ d ih =>
    rw [descend,ih,show k+(d+1)-1=(k+d-1)+1 by omega,nodes]
    rw [show k+d-1+1=k+d by omega]

theorem advance_mod (K k : Nat) (p : Node) (b : Bool) (hK : K≤k) :
    (advance k p b).r%2^K=p.r%2^K := by
  change (p.r+2^k*((p.a+(if b then p.r+3+k else 0))%2))%2^K=p.r%2^K
  have hd := Nat.pow_dvd_pow 2 hK
  obtain ⟨m,hm⟩ := hd
  rw [hm,Nat.mul_assoc,Nat.add_mul_mod_self_left]

theorem descend_filter (K k d r : Nat) (ps : List Node) (hK : K≤k) (p : Node) :
    p∈descend k d (ps.filter fun q=>q.r%2^K==r) ↔
      p∈descend k d ps ∧ p.r%2^K=r := by
  induction d generalizing p with
  | zero => simp [descend]
  | succ d ih =>
    simp only [descend,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro ⟨q,hq,rfl|rfl⟩
      · obtain ⟨hmem,hr⟩ := (ih q).mp hq
        exact ⟨⟨q,hmem,Or.inl rfl⟩,by rw [advance_mod K (k+d) q false (by omega),hr]⟩
      · obtain ⟨hmem,hr⟩ := (ih q).mp hq
        exact ⟨⟨q,hmem,Or.inr rfl⟩,by rw [advance_mod K (k+d) q true (by omega),hr]⟩
    · rintro ⟨⟨q,hq,rfl|rfl⟩,hr⟩
      · refine ⟨q,(ih q).mpr ⟨hq,?_⟩,Or.inl rfl⟩
        rwa [advance_mod K (k+d) q false (by omega)] at hr
      · refine ⟨q,(ih q).mpr ⟨hq,?_⟩,Or.inr rfl⟩
        rwa [advance_mod K (k+d) q true (by omega)] at hr

def pack (k : Nat) (ps : List Node) : Nat :=
    ps.foldl (fun a p=>a ||| 2^(p.r/2^k)) 0

theorem pack_bit_aux (k j a : Nat) (ps : List Node) :
    (ps.foldl (fun a p=>a ||| 2^(p.r/2^k)) a).testBit j=true ↔
      a.testBit j=true ∨ ∃ p∈ps, p.r/2^k=j := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,List.mem_cons]
    constructor
    · rintro ((ha|hp)|⟨q,hq,hj⟩)
      · exact Or.inl ha
      · exact Or.inr ⟨p,Or.inl rfl,hp⟩
      · exact Or.inr ⟨q,Or.inr hq,hj⟩
    · rintro (ha|⟨q,rfl|hq,hj⟩)
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr hj)
      · exact Or.inr ⟨q,hq,hj⟩

theorem pack_bit (k j : Nat) (ps : List Node) :
    (pack k ps).testBit j=true ↔ ∃ p∈ps, p.r/2^k=j := by
  simp [pack,pack_bit_aux]

def localMask (k d r : Nat) : Nat :=
  pack k (descend k d ((nodes (k-1)).filter fun p=>p.r%2^k==r))

/-- Exact dyadic support split into low-prefix rows and packed high bits.
The same proof works at every positive base depth and any extension depth. -/
theorem width_pos_iff_mask (k d n : Nat) (hk : 0<k) :
    0<width (k+d) n ↔ (localMask k d (n%2^k)).testBit ((n%2^(k+d))/2^k)=true := by
  have hmod : (n%2^(k+d))%2^k=n%2^k := Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 (by omega))
  have hwidth : 0<width (k+d) n ↔ ∃ p∈nodes (k+d-1), p.r=n%2^(k+d) := by
    have h := width_pos_iff_nodes (k+d-1) n
    rw [show k+d-1+1=k+d by omega] at h
    exact h
  rw [hwidth,localMask,pack_bit]
  constructor
  · rintro ⟨p,hp,hr⟩
    refine ⟨p,?_,by rw [hr]⟩
    apply (descend_filter k k d (n%2^k) _ (by omega) p).mpr
    rw [descend_nodes k d hk]
    exact ⟨hp,by rw [hr,hmod]⟩
  · rintro ⟨p,hp,hr⟩
    obtain ⟨hmem,hrem⟩ := (descend_filter k k d (n%2^k) _ (by omega) p).mp hp
    rw [descend_nodes k d hk] at hmem
    refine ⟨p,hmem,?_⟩
    have hdiv := Nat.mod_add_div p.r (2^k)
    rw [hrem,hr,←hmod] at hdiv
    exact hdiv.symm.trans (Nat.mod_add_div _ _)

theorem critical_reset_requires_mask (k d n : Nat) (hk : 0<k) (hn : 14≤n) (hKn : k+d≤n)
    (h : BB6.Agent1.Reach 2 (14*2^n-2*n-10)) :
    (localMask k d (n%2^k)).testBit ((n%2^(k+d))/2^k)=true := by
  apply (width_pos_iff_mask k d n hk).mp
  exact BB6.P1CarryExact.critical_reset_requires_width_full n (k+d) (by omega) hn hKn h

#print axioms width_pos_iff_mask
#print axioms critical_reset_requires_mask
end BB6.Agent9AffineResidue

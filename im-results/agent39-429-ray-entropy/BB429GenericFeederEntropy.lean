import BB429AllRayGlobal
import Lean.Elab.Tactic.Omega

namespace BB429InverseWord

/-- Any two source-rooted odd or even affine-ray targets admitting the same
length-k inverse word have the same first-coordinate residue mod 2^k. -/
theorem anyRayWord_mod (c k a a':Nat)
    (hr:AnyRayCandidate c a) (hr':AnyRayCandidate c a')
    (ha:16*2^k≤a+3) (ha':16*2^k≤a'+3)
    (hw:chosenAnyRayWord c k a=chosenAnyRayWord c k a') :
    a%(2^k)=a'%(2^k) := by
  obtain ⟨hlen,_,b,x,y,_,hbal,hchain⟩ := chosenAnyRayWord_spec c k a hr ha
  obtain ⟨hlen',_,b',x',y',_,hbal',hchain'⟩ := chosenAnyRayWord_spec c k a' hr' ha'
  have hc2 : HighChain a' b' (chosenAnyRayWord c k a) x' y' := by
    rw [hw]; exact hchain'
  by_cases hh:a'≤a
  · have ht := original_same_word_unique c a b a' b' hbal hbal' hh hchain hc2
    exact congruence_of_dvd_sub (2^k) a a' hh (by simpa [hlen] using ht)
  · have hh':a≤a' := by omega
    have ht := original_same_word_unique c a' b' a b hbal' hbal hh' hc2 hchain
    exact (congruence_of_dvd_sub (2^k) a' a hh' (by simpa [hlen] using ht)).symm

/-- General affine carry cancellation; the q0 factor 24 and constant 19
are inessential. -/
theorem generic_affine_correction_mod (M D e u v a a' : Nat)
    (h1:M ∣ a+D*u+e) (h2:M ∣ a'+D*v+e)
    (hm:a%M=a'%M) : (D*u)%M=(D*v)%M := by
  obtain ⟨p,hp⟩ := h1
  obtain ⟨q,hq⟩ := h2
  obtain ⟨r,s,hr⟩ := Nat.mod_eq_mod_iff.mp hm
  apply Nat.mod_eq_mod_iff.mpr
  refine ⟨q+s,p+r,?_⟩
  simp only [Nat.add_mul, Nat.mul_comm M] at *
  omega

/-- Cancel s binary factors of a general correction coefficient 2^s*d. -/
theorem generic_reduce_pow2 (k s d u v:Nat) (hs:s≤k)
    (hm:((2^s*d)*u)%(2^k)=((2^s*d)*v)%(2^k)) :
    (d*u)%(2^(k-s))=(d*v)%(2^(k-s)) := by
  have hpow : 2^k = 2^s*2^(k-s) := by
    calc
      2^k = 2^(s+(k-s)) := by congr 1; omega
      _ = 2^s*2^(k-s) := Nat.pow_add _ _ _
  obtain ⟨r,t,heq⟩ := Nat.mod_eq_mod_iff.mp hm
  apply Nat.mod_eq_mod_iff.mpr
  refine ⟨r,t,?_⟩
  have he : 2^s*(d*u+r*2^(k-s)) = 2^s*(d*v+t*2^(k-s)) := by
    calc
      2^s*(d*u+r*2^(k-s)) = (2^s*d)*u+r*2^k := by
        rw [hpow]
        simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
      _ = (2^s*d)*v+t*2^k := heq
      _ = 2^s*(d*v+t*2^(k-s)) := by
        rw [hpow]
        simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
  have hp : 0<2^s := Nat.two_pow_pos s
  exact Nat.eq_of_mul_eq_mul_left hp he

theorem generic_coefficient_inj (k s d X u v:Nat) (hs:s≤k)
    (hodd:d%2=1) (hX:X≤2^(k-s))
    (hu:u<X) (hv:v<X)
    (hm:((2^s*d)*u)%(2^k)=((2^s*d)*v)%(2^k)) : u=v := by
  have hc : Nat.Coprime (2^(k-s)) d :=
    ((odd_coprime_two d hodd).pow_left (k-s))
  have hh := coprime_mod_cancel (2^(k-s)) d u v hc
    (generic_reduce_pow2 k s d u v hs hm)
  have hu' : u%(2^(k-s))=u := Nat.mod_eq_of_lt (by omega)
  have hv' : v%(2^(k-s))=v := Nat.mod_eq_of_lt (by omega)
  omega

/-- A general two-choice-per-two-steps finite injection bound at any phase. -/
theorem any_phase_cardinality_bound (j k:Nat) (l:List Nat)
    (f:Nat→List Move) (huniq:l.Nodup)
    (hlegal:∀u∈l,Regular j (f u) ∧ (f u).length=k)
    (hinj:∀u∈l,∀v∈l,f u=f v→u=v) :
    l.length ≤ 2*2^(k/2) := by
  have hn : (l.map f).Nodup := nodup_map_inj_on l f huniq hinj
  have hsub : (l.map f) ⊆ allWords j k := by
    intro w hw
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hw
    obtain ⟨hr,hlen⟩ := hlegal u hu
    simpa [hlen] using regular_mem_allWords j hr
  have hh := List.Nodup.length_le_of_subset hn hsub
  have hh' := allWords_universal_bound j k
  rw [List.length_map] at hh
  omega

/-- Exact cardinality bound when the initial ray phase is even: one
choice-bearing letter per pair, with no leading factor of two. -/
theorem even_phase_cardinality_bound (j k:Nat) (l:List Nat)
    (f:Nat→List Move) (huniq:l.Nodup)
    (hlegal:∀u∈l,Regular j (f u) ∧ (f u).length=k)
    (hinj:∀u∈l,∀v∈l,f u=f v→u=v)
    (hj:j%2=0) :
    l.length ≤ 2^(k/2) := by
  have hn : (l.map f).Nodup := nodup_map_inj_on l f huniq hinj
  have hsub : (l.map f) ⊆ allWords j k := by
    intro w hw
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hw
    obtain ⟨hr,hlen⟩ := hlegal u hu
    simpa [hlen] using regular_mem_allWords j hr
  have hh := List.Nodup.length_le_of_subset hn hsub
  rw [List.length_map, allWords_len_even j k hj] at hh
  exact hh

/-- Generic source-root feeder sieve: no assumption about the formula for A(u)
or B(u) beyond a fixed affine ray, high-counter reachability, and a single
power-of-two congruence with a coefficient of known binary valuation. -/
theorem generic_feeder_cardinality_bound
    (c k s d e X:Nat) (A B:Nat→Nat)
    (l:List Nat) (hn:l.Nodup)
    (hs:s≤k) (hodd:d%2=1) (hX:X≤2^(k-s))
    (hl:∀u, u∈l → u<X ∧ BB429NewResidue.Reach (A u) (B u) ∧
      B u+c=2*(A u) ∧ 16*2^k≤A u+3 ∧
      2^k ∣ A u + (2^s*d)*u + e) :
    l.length ≤ 2*2^(k/2) := by
  classical
  let f:Nat→List Move := fun u => chosenAnyRayWord c k (A u)
  have hlegal : ∀u∈l, Regular (anyRayPhase c) (f u) ∧ (f u).length=k := by
    intro u hu
    obtain ⟨_,hreach,hbal,hhigh,hdiv⟩ := hl u hu
    obtain ⟨hlen,hr,_⟩ := chosenAnyRayWord_spec c k (A u)
      ⟨B u,hreach,hbal⟩ hhigh
    exact ⟨hr,hlen⟩
  have hinj : ∀u∈l,∀v∈l,f u=f v→u=v := by
    intro u hu v hv he
    obtain ⟨huX,huR,huB,huH,huDiv⟩ := hl u hu
    obtain ⟨hvX,hvR,hvB,hvH,hvDiv⟩ := hl v hv
    have hmod := anyRayWord_mod c k (A u) (A v)
      ⟨B u,huR,huB⟩ ⟨B v,hvR,hvB⟩ huH hvH he
    have haff := generic_affine_correction_mod (2^k) (2^s*d) e
      u v (A u) (A v) huDiv hvDiv hmod
    exact generic_coefficient_inj k s d X u v hs hodd hX huX hvX haff
  exact any_phase_cardinality_bound (anyRayPhase c) k l f hn hlegal hinj

/-- The same source-root feeder theorem with the sharper bound when the
offset induces an even initial phase. -/
theorem generic_feeder_cardinality_bound_even_phase
    (c k s d e X:Nat) (A B:Nat→Nat)
    (l:List Nat) (hn:l.Nodup)
    (hs:s≤k) (hodd:d%2=1) (hX:X≤2^(k-s))
    (hl:∀u, u∈l → u<X ∧ BB429NewResidue.Reach (A u) (B u) ∧
      B u+c=2*(A u) ∧ 16*2^k≤A u+3 ∧
      2^k ∣ A u + (2^s*d)*u + e)
    (hphase:(anyRayPhase c)%2=0) :
    l.length ≤ 2^(k/2) := by
  classical
  let f:Nat→List Move := fun u => chosenAnyRayWord c k (A u)
  have hlegal : ∀u∈l, Regular (anyRayPhase c) (f u) ∧ (f u).length=k := by
    intro u hu
    obtain ⟨_,hreach,hbal,hhigh,hdiv⟩ := hl u hu
    obtain ⟨hlen,hr,_⟩ := chosenAnyRayWord_spec c k (A u)
      ⟨B u,hreach,hbal⟩ hhigh
    exact ⟨hr,hlen⟩
  have hinj : ∀u∈l,∀v∈l,f u=f v→u=v := by
    intro u hu v hv he
    obtain ⟨huX,huR,huB,huH,huDiv⟩ := hl u hu
    obtain ⟨hvX,hvR,hvB,hvH,hvDiv⟩ := hl v hv
    have hmod := anyRayWord_mod c k (A u) (A v)
      ⟨B u,huR,huB⟩ ⟨B v,hvR,hvB⟩ huH hvH he
    have haff := generic_affine_correction_mod (2^k) (2^s*d) e
      u v (A u) (A v) huDiv hvDiv hmod
    exact generic_coefficient_inj k s d X u v hs hodd hX huX hvX haff
  exact even_phase_cardinality_bound (anyRayPhase c) k l f hn hlegal hinj hphase

#print axioms generic_feeder_cardinality_bound
#print axioms generic_feeder_cardinality_bound_even_phase
end BB429InverseWord

import NeedleCongruence

namespace NeedlePeriod
open NeedleCongruence

/-- Cancellation of a coprime natural multiplier in signed divisibility. -/
theorem cancel_coprime (M A : Nat) (x : Int) (h : M.Coprime A)
    (hd : (M:Int) ∣ (A:Int)*x) : (M:Int) ∣ x := by
  have hh := Int.natAbs_dvd_natAbs.mpr hd
  rw [Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast] at hh
  exact Int.natAbs_dvd_natAbs.mp (by simpa using h.dvd_of_dvd_mul_left hh)

theorem dvd_pow_sub (M : Nat) (x y : Int) (k : Nat) (h : (M:Int) ∣ x-y) :
    (M:Int) ∣ x^k-y^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨a,ha⟩ := ih
    obtain ⟨b,hb⟩ := h
    refine ⟨a*x+y^k*b,?_⟩
    rw [Int.pow_succ,Int.pow_succ]
    grind

/-- The elementary multiplicative period bound needed for the affine map. -/
theorem unit_period (u M : Nat) (hM : 1<M) (hu : u.Coprime M) :
    ∃ e : Nat, 0<e ∧ e<M ∧ (M:Int) ∣ (u:Int)^e-1 := by
  classical
  by_cases hnone : ∃ e : Nat, 0<e ∧ e<M ∧ (M:Int) ∣ (u:Int)^e-1
  · exact hnone
  exfalso
  let f : Nat → Nat := fun i => u^i%M
  have hne (i : Nat) : f i ≠ 0 := by
    intro hh
    have hd : M ∣ u^i := Nat.dvd_of_mod_eq_zero hh
    have hc := Nat.coprime_comm.mp (hu.pow_left i)
    have hm : M ∣ 1 := hc.dvd_of_dvd_mul_left (by simpa using hd)
    have hle := Nat.le_of_dvd (by decide : 0<1) hm
    omega
  have hcollision (i j : Nat) (hij : i<j) (hj : j<M) : f i ≠ f j := by
    intro hh
    have he : ((u:Int)^j)%(M:Int)=((u:Int)^i)%(M:Int) := by
      have hcast := congrArg (fun x : Nat => (x:Int)) hh.symm
      simpa [f,Int.natCast_emod,Int.natCast_pow] using hcast
    have hd : (M:Int) ∣ (u:Int)^j-(u:Int)^i :=
      Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he)
    have hfactor : (u:Int)^j-(u:Int)^i=(u:Int)^i*((u:Int)^(j-i)-1) := by
      have hs : j=i+(j-i) := by omega
      have hpow : (u:Int)^j=(u:Int)^i*(u:Int)^(j-i) := by rw [←Int.pow_add,←hs]
      rw [hpow]
      grind
    rw [hfactor] at hd
    have hdiv := cancel_coprime M (u^i) ((u:Int)^(j-i)-1) (Nat.coprime_comm.mp (hu.pow_left i)) (by simpa using hd)
    exact hnone ⟨j-i,by omega,by omega,hdiv⟩
  let xs := (List.range M).map f
  have hn : xs.Nodup := by
    dsimp [xs]
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro i j hi hj hij
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    by_cases hlt : i<j
    · exact hcollision i j hlt hj'
    · exact Ne.symm (hcollision j i (by omega) hi')
  have hsub : xs ⊆ List.range' 1 (M-1) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hlt : f i<M := Nat.mod_lt _ (by omega)
    have hpos := hne i
    apply List.mem_range'_1.mpr
    omega
  have hlen := hn.length_le_of_subset hsub
  simp [xs] at hlen
  omega

theorem period_shift (u M e v j : Nat) (h : (M:Int) ∣ (u:Int)^e-1) :
    (M:Int) ∣ (u:Int)^(v+e*j)-(u:Int)^v := by
  have hh := dvd_pow_sub M ((u:Int)^e) 1 j h
  rw [←Int.pow_mul] at hh
  rw [Int.pow_add]
  obtain ⟨z,hz⟩ := hh
  refine ⟨(u:Int)^v*z,?_⟩
  grind

/-- Every integer-affine exponential map v + A*u^v+B is surjective
modulo any positive modulus coprime to u, even with v arbitrarily large. -/
theorem affine_exponential_surjective (M u : Nat) (hM : 0<M) (hu : u.Coprime M)
    (A B R : Int) (N : Nat) : ∃ v : Nat, N≤v ∧ (M:Int) ∣ (v:Int)+A*(u:Int)^v+B-R := by
  induction M using Nat.strongRecOn generalizing N with
  | ind M ih =>
    by_cases hm : M=1
    · subst M; exact ⟨N,by omega,by simp⟩
    obtain ⟨e,he,heM,hperiod⟩ := unit_period u M (by omega) hu
    let g := e.gcd M
    have hgpos : 0<g := Nat.gcd_pos_of_pos_right e hM
    have hglt : g<M := Nat.lt_of_le_of_lt (Nat.gcd_le_left M he) heM
    have hgdiv : g∣M := Nat.gcd_dvd_right e M
    have hgc : u.Coprime g := Nat.Coprime.coprime_dvd_right hgdiv hu
    obtain ⟨v,hv,hgv⟩ := ih g hglt hgpos hgc N
    let C : Int := (v:Int)+A*(u:Int)^v+B
    have hsolve : (e.gcd M:Int) ∣ R-C := by
      dsimp [C]
      change (g:Int) ∣ _
      obtain ⟨z,hz⟩ := hgv
      exact ⟨-z,by grind⟩
    obtain ⟨j,hj,hjdiv⟩ := linear_solve e M C R 0 hM hsolve
    refine ⟨v+e*j,by omega,?_⟩
    obtain ⟨a,ha⟩ := hjdiv
    obtain ⟨b,hb⟩ := period_shift u M e v j hperiod
    refine ⟨a+A*b,?_⟩
    push_cast
    dsimp [C] at ha
    grind

#print axioms unit_period
#print axioms affine_exponential_surjective
end NeedlePeriod

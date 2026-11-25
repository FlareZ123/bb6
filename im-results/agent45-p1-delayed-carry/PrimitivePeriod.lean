import PeriodicObstruction
namespace BB6.Agent45WeightedDigitGap

/-- A period of a rational binary word is primitive if no smaller positive
    shift fixes the corresponding residue modulo 2^p-1. -/
def Primitive (p U : Nat) : Prop := ∀ j, 0<j → j<p → ¬ (2^p-1) ∣ U*(2^j-1)

theorem odd_coprime_two (D : Nat) (h : D%2=1) : Nat.Coprime D 2 := by
  rw [Nat.Coprime,Nat.gcd_comm D 2,Nat.gcd_rec 2 D,h,Nat.gcd_one_left]

theorem odd_coprime_pow (D : Nat) (h : D%2=1) (j : Nat) : Nat.Coprime D (2^j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.pow_succ,Nat.coprime_mul_iff_right]; exact ⟨ih,odd_coprime_two D h⟩

theorem mersenne_odd (p : Nat) (hp : 0<p) : (2^p-1)%2=1 := by
  cases p with
  | zero => omega
  | succ p => rw [Nat.pow_succ]; have := Nat.two_pow_pos p; omega

theorem primitive_no_dvd (p U : Nat) (hp : 0<p) (hU : 0<U) (hUD : U<2^p-1)
    (hprim : Primitive p U) : ¬ (2^p-1) ∣ p*U := by
  intro hd
  let D := 2^p-1
  have hD : 0<D := by omega
  have hodd : D%2=1 := mersenne_odd p hp
  let R := fun i : Nat => (U*2^i)%D
  have hRlt (i : Nat) : R i<D := Nat.mod_lt _ hD
  have hRpos (i : Nat) : 0<R i := by
    by_cases hz : R i=0
    · have hh : D ∣ U*2^i := Nat.dvd_of_mod_eq_zero hz
      have hu := (odd_coprime_pow D hodd i).dvd_of_dvd_mul_right hh
      have := Nat.le_of_dvd hU hu
      omega
    · omega
  have hRd (i : Nat) : D ∣ p*R i := by
    have hh : D ∣ (p*U)*2^i := Nat.dvd_mul_right_of_dvd hd _
    rw [Nat.mul_assoc] at hh
    apply Nat.dvd_of_mod_eq_zero
    change (p*((U*2^i)%D))%D=0
    rw [Nat.mul_mod, Nat.mod_mod, ←Nat.mul_mod]
    exact Nat.mod_eq_zero_of_dvd hh
  let f := fun i : Nat => p*R i/D
  have hf (i : Nat) : D*f i=p*R i := Nat.mul_div_cancel' (hRd i)
  have hfpos (i : Nat) : 0<f i := by
    have h := hf i
    have hh := Nat.mul_pos hp (hRpos i)
    by_cases hz : f i=0
    · rw [hz,Nat.mul_zero] at h; omega
    · omega
  have hflt (i : Nat) : f i<p := by
    have h := hf i
    have hh := Nat.mul_lt_mul_of_pos_left (hRlt i) hp
    rw [Nat.mul_comm p D] at hh
    exact Nat.lt_of_mul_lt_mul_left (by omega : D*f i<D*p)
  have hinj (i j : Nat) (hij : i<j) (hj : j<p) : f i≠f j := by
    intro he
    have hi := hf i
    have hj' := hf j
    rw [he,hj'] at hi
    have hr : R i=R j := Nat.eq_of_mul_eq_mul_left hp hi.symm
    have hpow : 2^j=2^i*2^(j-i) := by rw [←Nat.pow_add,show i+(j-i)=j by omega]
    have hd1 := Nat.div_add_mod (U*2^i) D
    have hd2 := Nat.div_add_mod (U*2^j) D
    change D*(U*2^i/D)+R i=U*2^i at hd1
    change D*(U*2^j/D)+R j=U*2^j at hd2
    rw [←hr] at hd2
    have hsub : U*2^i*(2^(j-i)-1)=U*2^j-U*2^i := by
      rw [Nat.mul_sub,Nat.mul_one,hpow]; ac_rfl
    have hdiv : D ∣ U*2^j-U*2^i := by
      have hm : U*2^j-U*2^i=D*(U*2^j/D-U*2^i/D) := by
        calc
          _ = (D*(U*2^j/D)+R i)-(D*(U*2^i/D)+R i) := by omega
          _ = _ := by rw [Nat.add_sub_add_right,Nat.mul_sub]
      rw [hm]; exact Nat.dvd_mul_right _ _
    rw [←hsub] at hdiv
    have hdiv' : D ∣ (U*(2^(j-i)-1))*2^i := by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hdiv
    exact hprim (j-i) (by omega) (by omega) ((odd_coprime_pow D hodd i).dvd_of_dvd_mul_right hdiv')
  have hnd : ((List.range p).map f).Nodup := by
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map,List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_range]
    exact hinj i j hij (by simpa using hj)
  have hsub : (List.range p).map f ⊆ List.range' 1 (p-1) := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    apply List.mem_range'.2
    exact ⟨f i-1,by have := hfpos i; have := hflt i; omega,by have := hfpos i; omega⟩
  have hlen := hnd.length_le_of_subset hsub
  simp only [List.length_map,List.length_range,List.length_range'] at hlen
  omega

theorem primitive_numerator_nonzero (A s p V U : Nat) (hp : 0<p) (hV : V<2^s)
    (hU : U<2^p) (hprim : Primitive p U) : periodicNumerator A s p V U≠0 := by
  by_cases hz : U=0
  · rw [hz]; exact zero_block_nonzero A s p V hp hV
  by_cases ho : U=2^p-1
  · rw [ho]; exact ones_block_nonzero A s p V hp hV
  intro he
  let D := 2^p-1
  have hD : (D:Int)=(2:Int)^p-1 := by
    dsimp [D]; rw [Int.natCast_sub (by have := Nat.two_pow_pos p; omega : 1≤2^p),Int.natCast_pow]; rfl
  unfold periodicNumerator at he
  dsimp only at he
  rw [←hD] at he
  have hI : (D:Int) ∣ (2:Int)^s*(p:Int)*U*(2:Int)^p := by
    refine ⟨((2:Int)^s*((digitWeight p U:Int)+((s:Int)-A)*U)-((digitWeight s V:Int)-(A:Int)*V-1)*(D:Int)),?_⟩
    grind
  have hN : D ∣ 2^s*p*U*2^p := by
    apply Int.natCast_dvd_natCast.mp
    simp only [Int.natCast_mul,Int.natCast_pow]; exact hI
  have hc := odd_coprime_pow D (mersenne_odd p hp)
  have hh := (hc p).dvd_of_dvd_mul_right hN
  rw [show 2^s*p*U=(2^s)*(p*U) by ac_rfl] at hh
  have hd := (hc s).dvd_of_dvd_mul_left hh
  exact primitive_no_dvd p U hp (by omega) (by omega) hprim hd

/-- A primitive repeated tail is impossible once its exact numerator is
    smaller in absolute value than the modulus of the trace. -/
theorem no_primitive_repeated_trace (n A s p V U t a : Nat)
    (hn : 0<n) (heven : n%2=0)
    (hA : BB6.Agent45.DelayedCarry.total n=n+3+A)
    (hp : 0<p) (hV : V<2^s) (hU : U<2^p) (hprim : Primitive p U)
    (hsize : (periodicNumerator A s p V U).natAbs<2^(s+p*t)) :
    ¬ BB6.Agent45.DelayedCarry.Trace n (s+p*t) (V+2^s*(U*geom (2^p) t)) a := by
  intro h
  have hd := trace_periodic_dvd n A s p V U t a hn heven hA hV hU h
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa [Int.natAbs_pow] using hsize)
  exact primitive_numerator_nonzero A s p V U hp hV hU hprim hzero

#print axioms primitive_no_dvd
#print axioms primitive_numerator_nonzero
#print axioms no_primitive_repeated_trace
end BB6.Agent45WeightedDigitGap

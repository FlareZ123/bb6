import NeedleMixed

namespace NeedleCoherent
open NeedleWord NeedleCongruence NeedleMixed

theorem path_append {w z : List Nat} {p b c : Nat} (h : Path w p b) (h' : Path z b c) :
    Path (w++z) p c := by
  induction h with
  | nil => simpa using h'
  | cons v q hp hb rest ih => exact Path.cons v q hp hb (ih h')

theorem product_pos (w : List Nat) : 0<L w := by
  have h := product_odd w
  omega

/-- Every positive integer either is a terminal power or has a legal edge. -/
theorem factor_or_power (x : Nat) (hx : 0<x) :
    (∃ k : Nat, x=2^k) ∨ (∃ v q : Nat, x=2^v*(2*q+3)) := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hodd : x%2=1
    · by_cases h1 : x=1
      · exact Or.inl ⟨0,by simpa using h1⟩
      right
      refine ⟨0,(x-3)/2,?_⟩
      simp; omega
    · have hdiv : x=2*(x/2) := by omega
      have hpos : 0<x/2 := by omega
      have hlt : x/2<x := by omega
      rcases ih (x/2) hlt hpos with ⟨k,hk⟩ | ⟨v,q,hvq⟩
      · left; refine ⟨k+1,?_⟩; rw [Nat.pow_succ]; omega
      · right; refine ⟨v+1,q,?_⟩; rw [Nat.pow_succ]; grind

theorem powers_gap (x y : Nat) (_hx : 0<x) (hxy : x<y) (hsmall : y<2*x) :
    ¬ ((∃ k : Nat, x=2^k) ∧ (∃ l : Nat, y=2^l)) := by
  rintro ⟨⟨k,hk⟩,⟨l,hl⟩⟩
  have hkl : k<l := by
    by_cases hh : l≤k
    · have hh' := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hh
      omega
    · omega
  have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show k+1≤l by omega)
  rw [Nat.pow_succ] at hp
  omega

/-- No positive-step progression is eventually made of terminal powers. -/
theorem progression_legal (a A N : Nat) (hA : 0<A) :
    ∃ j v q : Nat, N≤j ∧ a+A*j=2^v*(2*q+3) := by
  let j := N+3
  let x := a+A*j
  let y := a+A*(j+1)
  have hx : A<x := by
    dsimp [x,j]
    have hmul : A*1<A*(N+3) := Nat.mul_lt_mul_of_pos_left (by omega) hA
    omega
  have hy : y=x+A := by simp [x,y,Nat.mul_add,Nat.add_assoc]
  rcases factor_or_power x (by omega) with hxpow | ⟨v,q,hv⟩
  · rcases factor_or_power y (by omega) with hypow | ⟨v,q,hv⟩
    · exact False.elim (powers_gap x y (by omega) (by omega) (by omega) ⟨hxpow,hypow⟩)
    · exact ⟨j+1,v,q,by dsimp [j]; omega,hv⟩
  · exact ⟨j,v,q,by dsimp [j]; omega,hv⟩

/-- Every congruence class admits arbitrarily long genuine paths, with
arbitrarily large starts. No compatibility between different witnesses is assumed. -/
theorem path_from_class (P r N t : Nat) (hP : 0<P) :
    ∃ w : List Nat, ∃ p c : Nat, w.length=t ∧ N≤p ∧ p%P=r%P ∧ Path w p c := by
  induction t with
  | zero =>
    let p := r+P*N
    refine ⟨[],p,p,rfl,?_,?_,Path.nil p⟩
    · have hh : N≤P*N := Nat.le_mul_of_pos_left N hP
      omega
    · simp [p,Nat.add_mod]
  | succ t ih =>
    obtain ⟨w,p,c,hw,hN,hr,hpath⟩ := ih
    have hprod : 0<L w*P := Nat.mul_pos (product_pos w) hP
    obtain ⟨j,v,q,_,hq⟩ := progression_legal c (L w*P) 0 hprod
    have ht := path_transport hpath (P*j)
    have hce : c+L w*(P*j)=2^v*(2*q+3) := by rw [←hq]; ac_rfl
    let c' := c+L w*(P*j)+v+3*(q+1)
    have htail : Path [v] (c+L w*(P*j)) c' := Path.cons v q hce rfl (Path.nil c')
    refine ⟨w++[v],p+2^S w*(P*j),c',by simp [hw],by omega,?_,path_append ht htail⟩
    have he : 2^S w*(P*j)=P*(2^S w*j) := by ac_rfl
    rw [he,Nat.add_mod,Nat.mul_mod]
    simpa using hr

/-- Once the prefix has consumed at least h dyadic bits, a translated copy
of that exact prefix can be followed by one actual edge to any prescribed
class modulo 2^h*M. The original start class is retained. -/
theorem coherent_extend (M h : Nat) (hodd : M%2=1) {w : List Nat} {p c : Nat}
    (hpref : Path w p c) (hs : h≤S w) (target N : Nat) :
    ∃ v p' c' : Nat, N≤p' ∧ p'%(2^h*M)=p%(2^h*M) ∧
      c'%(2^h*M)=target%(2^h*M) ∧ Path (w++[v]) p' c' := by
  let A := L w*M
  have hAodd : A%2=1 := by simp [A,Nat.mul_mod,product_odd,hodd]
  have hA : 0<A := by omega
  obtain ⟨v,q,b,z,_,hq,hb,hz,hbA,hzA,hz2⟩ := mixed_edge A h hAodd c target target 0 (c+A*N)
  have hbq : q≤b := by
    have h2 := Nat.two_pow_pos v
    have hh := Nat.le_mul_of_pos_left (2*q+3) h2
    omega
  have hbge : c≤b := by omega
  have hbdiv : A∣b-c := by
    apply Int.ofNat_dvd.mp
    rw [Int.natCast_sub hbge]
    exact hbA
  obtain ⟨j,hj⟩ := hbdiv
  have hjN : N≤j := by
    by_cases hjlt : j<N
    · have hh := Nat.mul_lt_mul_of_pos_left hjlt hA
      omega
    · omega
  have hbc : b=c+L w*(M*j) := by dsimp [A] at hj; grind
  have ht := path_transport hpref (M*j)
  rw [←hbc] at ht
  have ht2 : Path [v] b z := Path.cons v q hb hz (Path.nil z)
  let p' := p+2^S w*(M*j)
  refine ⟨v,p',z,?_,?_,?_,path_append ht ht2⟩
  · have hM : 0<M := by omega
    have hm := Nat.le_mul_of_pos_left j hM
    have h2 := Nat.le_mul_of_pos_left (M*j) (Nat.two_pow_pos (S w))
    omega
  · obtain ⟨d,hd⟩ := Nat.pow_dvd_pow 2 hs
    have he : p'=p+(2^h*M)*(d*j) := by dsimp [p']; rw [hd]; ac_rfl
    rw [he,Nat.add_mod,Nat.mul_mod]
    simp
  · have hzM : (M:Int) ∣ (z:Int)-(target:Int) := by
      have hMA : (M:Int) ∣ (A:Int) := by dsimp [A]; push_cast; exact Int.dvd_mul_left _ _
      exact Int.dvd_trans hMA hzA
    have hN1 := Int.natAbs_dvd_natAbs.mpr hzM
    have hN2 := Int.natAbs_dvd_natAbs.mpr hz2
    simp [Int.natAbs_pow] at hN1 hN2
    have hcop := Nat.coprime_comm.mp (odd_coprime_pow M h hodd)
    have hboth := hcop.mul_dvd_of_dvd_of_dvd hN2 hN1
    have hI : ((2^h*M:Nat):Int) ∣ (z:Int)-(target:Int) := by
      apply Int.natAbs_dvd_natAbs.mp
      rw [Int.natAbs_natCast]
      exact hboth
    have he := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hI)
    exact_mod_cast he

/-- Coherent mixed-modulus completeness, in at most h+1 (in fact exactly
h+1) successful steps. Both endpoints are from a single actual path. -/
theorem coherent_classes (M h r target N : Nat) (hodd : M%2=1) :
    ∃ w : List Nat, ∃ p c : Nat, w.length=h+1 ∧ N≤p ∧
      p%(2^h*M)=r%(2^h*M) ∧ c%(2^h*M)=target%(2^h*M) ∧ Path w p c := by
  have hP : 0<2^h*M := Nat.mul_pos (Nat.two_pow_pos h) (by omega)
  obtain ⟨w,p,c,hw,_,hr,hp⟩ := path_from_class (2^h*M) r N h hP
  have hs := weight_ge_length w
  obtain ⟨v,p',c',hN,hr',hc',hp'⟩ := coherent_extend M h hodd hp (by omega) target N
  refine ⟨w++[v],p',c',by simp [hw],hN,hr'.trans hr,hc',hp'⟩

#print axioms factor_or_power
#print axioms path_from_class
#print axioms coherent_extend
#print axioms coherent_classes
end NeedleCoherent

import AsymmetricRotation

namespace NeedleRotation.Asymmetric

/-- Rational exponent bound without rounding q to a multiple of five. -/
theorem pow3_ceil (q : Nat) : (3:Nat)^q≤2^((8*q+4)/5) := by
  let H:=(8*q+4)/5
  have hq : 8*q≤5*H := by dsimp [H]; omega
  have hpow : ((3:Nat)^q)^5≤(2^H)^5 := by
    calc
      (3^q)^5 = (3^5)^q := by rw [←Nat.pow_mul,←Nat.pow_mul,Nat.mul_comm q 5]
      _ ≤ (2^8)^q := Nat.pow_le_pow_left (by decide) _
      _ = 2^(8*q) := (Nat.pow_mul _ _ _).symm
      _ ≤ 2^(5*H) := Nat.pow_le_pow_right (by decide) hq
      _ = (2^H)^5 := by rw [←Nat.pow_mul,Nat.mul_comm H 5]
  by_cases h : (3:Nat)^q≤2^H
  · exact h
  · have hn := Nat.pow_lt_pow_left (by omega : 2^H<3^q) (by decide : 5≠0)
    omega

/-- The two-term terminal dichotomy with asymptotic coefficient 8/5
    instead of 2 in the quotient term. -/
theorem two_term_narrow (n m H : Nat) (C : Int)
    (hm : 0<m) (hH : 0<H) (hc : C%2=1) (hC : C.natAbs<2^H)
    (hsize : H+(8*(n/m+1)+4)/5+1≤m)
    (hd : denominator m∣(2:Int)^n+C) :
    n%m=0 ∧ C= -(-3:Int)^(n/m) := by
  let k:=n/m
  let t:=n%m
  have ht : t<m := Nat.mod_lt _ hm
  have hnt : n=m*k+t := (Nat.div_add_mod n m).symm
  have two_even (z : Nat) (hz : 0<z) : ((2:Int)^z)%2=0 := by
    obtain ⟨i,rfl⟩ : ∃ i : Nat, z=i+1 := ⟨z-1,by omega⟩
    rw [Int.pow_succ,Int.mul_emod]
    simp
  have hDabs : (denominator m).natAbs=2^m+3 := by
    simp [denominator, Int.natAbs_pow, Int.natAbs_add_of_nonneg, Int.pow_nonneg]
  have hD : denominator m∣(-3:Int)^k*2^t+C := by
    have h := rotated_divisibility m 0 [(1,n),(C,0)] (by simpa [value] using hd)
    simpa [rotate,rotateTerm,value,k,t] using h
  have h2 : 2^(m-1)+2^(m-1)=(2:Nat)^m := by
    have heq : m-1+1=m := by omega
    have hp : 2^(m-1+1)=(2:Nat)^(m-1)*2 := Nat.pow_succ 2 _
    rw [heq] at hp
    omega
  by_cases hlo : t≤H
  · have hpow : (3:Nat)^k*2^t≤2^(m-1) := by
      calc
        3^k*2^t ≤ 2^((8*k+4)/5)*2^t := Nat.mul_le_mul_right _ (pow3_ceil k)
        _ = 2^((8*k+4)/5+t) := (Nat.pow_add 2 _ _).symm
        _ ≤ 2^(m-1) := Nat.pow_le_pow_right (by decide) (by dsimp [k] at *; omega)
    have hcsmall : C.natAbs<2^(m-1) := Nat.lt_of_lt_of_le hC (Nat.pow_le_pow_right (by decide) (by omega))
    have habs := Int.natAbs_add_le ((-3:Int)^k*2^t) C
    simp only [Int.natAbs_mul,Int.natAbs_pow] at habs
    change ((-3:Int)^k*2^t+C).natAbs≤3^k*2^t+C.natAbs at habs
    have hz : (-3:Int)^k*2^t+C=0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hD (by rw [hDabs]; omega)
    have ht0 : t=0 := by
      by_cases h : t=0
      · exact h
      have hmod := congrArg (fun x : Int => x%2) hz
      rw [Int.add_emod,Int.mul_emod,two_even t (by omega),hc] at hmod
      simp at hmod
    rw [ht0,Int.pow_zero,Int.mul_one] at hz
    exact ⟨ht0,by change C= -(-3:Int)^k; omega⟩
  · let h:=m-t
    have hh : h<m := by dsimp [h]; omega
    have hhpos : 0<h := by dsimp [h]; omega
    have he : n+h=m*(k+1) := by rw [hnt]; dsimp [h]; rw [Nat.mul_add]; omega
    have hquo : (n+h)/m=k+1 := by rw [he,Nat.mul_div_cancel_left _ hm]
    have hrem : (n+h)%m=0 := by rw [he,Nat.mul_mod_right]
    have hd2 : denominator m∣(-3:Int)^(k+1)+C*2^h := by
      have hx := rotated_divisibility m h [(1,n),(C,0)] (by simpa [value] using hd)
      simpa [rotate,rotateTerm,value,hquo,hrem,Nat.div_eq_of_lt hh,Nat.mod_eq_of_lt hh] using hx
    have hP : (3:Nat)^(k+1)≤2^(m-1) := Nat.le_trans (pow3_ceil _) (Nat.pow_le_pow_right (by decide) (by dsimp [k] at *; omega))
    have hCP : C.natAbs*2^h<2^(m-1) := by
      calc
        C.natAbs*2^h < 2^H*2^h := Nat.mul_lt_mul_of_pos_right hC (Nat.two_pow_pos _)
        _=2^(H+h) := (Nat.pow_add 2 _ _).symm
        _≤2^(m-1) := Nat.pow_le_pow_right (by decide) (by dsimp [h]; omega)
    have habs := Int.natAbs_add_le ((-3:Int)^(k+1)) (C*2^h)
    simp only [Int.natAbs_pow,Int.natAbs_mul] at habs
    change ((-3:Int)^(k+1)+C*2^h).natAbs≤3^(k+1)+C.natAbs*2^h at habs
    have hz : (-3:Int)^(k+1)+C*2^h=0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd2 (by rw [hDabs]; omega)
    have hmod := congrArg (fun x : Int => x%2) hz
    have hodd : ((-3:Int)^(k+1))%2=1 := by simpa using odd_mul_neg_three_pow 1 (k+1) (by decide)
    rw [Int.add_emod,hodd,Int.mul_emod,two_even h hhpos] at hmod
    simp at hmod

#print axioms pow3_ceil
#print axioms two_term_narrow
end NeedleRotation.Asymmetric

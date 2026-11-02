import Std

namespace BB6.Agent39Three

def W (d q : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => W d q n + q + d*(W d q n)*q

private theorem pow_mul_factor (d q t : Nat) :
    (1+d*t)*(1+d*q) = 1+d*(t+q+d*t*q) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

theorem pow_one_mod (d q n : Nat) :
    (1+d*q)^n = 1+d*W d q n := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
      rw [Nat.pow_succ, ih]
      simpa only [W] using pow_mul_factor d q (W d q n)

theorem W_mod_three (d q n : Nat) (hd : 3∣d) :
    W d q n %3 = (n*q)%3 := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
      obtain ⟨v,hv⟩ := hd
      have hz : d*(W d q n)*q=3*(v*(W d q n)*q) := by
        rw [hv]
        ac_rfl
      simp only [W, hz, Nat.add_mul]
      omega

end BB6.Agent39Three

namespace BB6.Agent39Three

def Q : Nat → Nat
  | 0 => 1
  | k+1 =>
    Q k * (1 + 3*(3^k*Q k) + (3^k*Q k)*(3*(3^k*Q k)))

theorem Q_mod_three (k : Nat) : Q k %3=1 := by
  induction k with
  | zero => decide
  | succ k ih =>
      let z := 3^k*Q k
      have hz : (1+3*z+z*(3*z)) = 1+3*(z+z*z) := by
        simp only [Nat.mul_add, Nat.add_mul]
        ac_rfl
      change (Q k*(1+3*z+z*(3*z)))%3=1
      rw [hz, Nat.mul_mod]
      have h1 : (1+3*(z+z*z))%3=1 := by omega
      rw [ih, h1]

end BB6.Agent39Three

namespace BB6.Agent39Three

private theorem cube_shift (z : Nat) :
    (z+1)^3 = 1 + z * ((z+1)*(z+1)+(z+1)+1) := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one,
             Nat.add_mul, Nat.mul_add, Nat.one_mul]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

private theorem div_three_factor (y : Nat) :
    ((3*y+1)*(3*y+1)+(3*y+1)+1) = 3*(1+3*y+y*(3*y)) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

private theorem cube_three (y : Nat) :
    (1+3*y)^3 = 1+9*y*(1+3*y+y*(3*y)) := by
  have hs:=cube_shift (3*y)
  have hfactor:=div_three_factor y
  have hc : 3*y+1=1+3*y := by omega
  rw [hc] at hs
  rw [hc] at hfactor
  rw [hfactor] at hs
  have hh : 9*y*(1+3*y+y*(3*y)) =
      (3*y)*(3*(1+3*y+y*(3*y))) := by
    have hn : 9=3*3 := rfl
    rw [hn]
    ac_rfl
  rwa [hh]

private theorem cube_lift (k q : Nat) :
    (1+3^(k+1)*q)^3 =
    1+3^(k+2)*(q*(1+3*(3^k*q)+(3^k*q)*(3*(3^k*q)))) := by
  have h1 : 3^(k+1) = 3*3^k := by rw [Nat.pow_succ]; omega
  have h2 : 3^(k+2) = 9*3^k := by
    have h : k+2=k+1+1 := by omega
    rw [h,Nat.pow_succ,Nat.pow_succ]
    omega
  rw [h1,h2]
  have he : 1+(3*3^k)*q = 1+3*(3^k*q) := by ac_rfl
  rw [he]
  rw [cube_three (3^k*q)]
  congr 1
  ac_rfl

theorem power_three_lifting (k : Nat) :
    2^(2*3^k) = 1 + 3^(k+1)*Q k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : 2*(3^(k+1)) = (2*3^k)*3 := by
      rw [Nat.pow_succ]
      omega
    calc
      2^(2*3^(k+1)) = (2^(2*3^k))^3 := by
        rw [hp,Nat.pow_mul]
      _ = (1+3^(k+1)*Q k)^3 := by rw [ih]
      _ = 1+3^(k+2)*(Q k*(1+3*(3^k*Q k)+(3^k*Q k)*(3*(3^k*Q k)))) :=
        cube_lift k (Q k)
      _ = 1+3^((k+1)+1)*Q (k+1) := by rfl

#print axioms power_three_lifting
#print axioms W_mod_three
#print axioms Q_mod_three
end BB6.Agent39Three

namespace BB6.Agent39Three

theorem W_div3_iff (d q k : Nat) (hd : 3∣d) (hq:q%3=1) :
    3 ∣ W d q k ↔ 3 ∣ k := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  rw [W_mod_three d q k hd]
  have he : (k*q)%3=k%3 := by
    rw [Nat.mul_mod, hq]
    omega
  rw [he]

/-- The precise next-level residue condition for a 3-adic unit base. -/
theorem pow_lift_iff (h q k : Nat) (hh:0<h) (hq:q%3=1) :
    (∃ m, (1+3^h*q)^k = 1+3^(h+1)*m) ↔ 3∣k := by
  have hd : 3 ∣ 3^h := by
    obtain ⟨h0,rfl⟩ : ∃ t, h=t+1 := ⟨h-1,by omega⟩
    rw [Nat.pow_succ]
    exact ⟨3^h0,by omega⟩
  have hpower : 0 < 3^h := Nat.pow_pos (by decide)
  have hp := pow_one_mod (3^h) q k
  constructor
  · rintro ⟨m,hm⟩
    have hW : W (3^h) q k=3*m := by
      apply Nat.mul_left_cancel hpower
      have hh1 : 1 + 3^h*W (3^h) q k = 1 + 3^h*(3*m) := by
        rw [←hp, hm, Nat.pow_succ]
        ac_rfl
      omega
    apply (W_div3_iff (3^h) q k hd hq).mp
    exact ⟨m,hW⟩
  · intro hk
    have hW : 3∣W (3^h) q k :=
      (W_div3_iff (3^h) q k hd hq).mpr hk
    obtain ⟨m,hm⟩ := hW
    refine ⟨m, ?_⟩
    rw [hp,hm,Nat.pow_succ]
    congr 1
    ac_rfl

#print axioms pow_lift_iff
end BB6.Agent39Three

namespace BB6.Agent39Three

/-- The first 3-adic level admits precisely even exponents. -/
theorem pow2_cong_three_iff_even (j : Nat) :
    (∃ q, 2^j=1+3*q) ↔ 2 ∣ j := by
  constructor
  · rintro ⟨q,hq⟩
    by_cases hj : j%2=0
    · exact (Nat.dvd_iff_mod_eq_zero).mpr hj
    · have hjodd : j%2=1 := by omega
      have he : j=2*(j/2)+1 := by omega
      have hp : 2^j=2*(1+3*W 3 1 (j/2)) := by
        calc
          2^j = 2^(2*(j/2)+1) := congrArg (fun e : Nat => 2^e) he
          _ = (2^2)^(j/2)*2 := by rw [Nat.pow_succ, Nat.pow_mul]
          _ = (1+3*W 3 1 (j/2))*2 := by
            rw [show (2:Nat)^2=1+3*1 by decide, pow_one_mod]
          _ = 2*(1+3*W 3 1 (j/2)) := by omega
      omega
  · rintro ⟨k,hj⟩
    refine ⟨W 3 1 k, ?_⟩
    rw [hj, Nat.pow_mul]
    have h4 : (2:Nat)^2=1+3*1 := by decide
    rw [h4, pow_one_mod]

#print axioms pow2_cong_three_iff_even
end BB6.Agent39Three

namespace BB6.Agent39Three

/-- Exact multiplicative order of 2 modulo every positive power of 3.
    The order modulo 3^(k+1) is 2*3^k. -/
theorem power_cong_iff_exponent (k j : Nat) :
    (∃ m, 2^j = 1+3^(k+1)*m) ↔ 2*3^k ∣ j := by
  induction k generalizing j with
  | zero =>
      simpa using pow2_cong_three_iff_even j
  | succ k ih =>
      have hQ : Q k %3=1 := Q_mod_three k
      have hpow := power_three_lifting k
      constructor
      · rintro ⟨m,hm⟩
        have hlow : ∃ z, 2^j=1+3^(k+1)*z := by
          refine ⟨3*m, ?_⟩
          calc
            2^j = 1+3^(k+1+1)*m := hm
            _ = 1+3^(k+1)*(3*m) := by rw [Nat.pow_succ]; ac_rfl
        obtain ⟨r,hr⟩ := (ih j).mp hlow
        have hbase : (1+3^(k+1)*Q k)^r = 1+3^((k+1)+1)*m := by
          calc
            (1+3^(k+1)*Q k)^r = (2^(2*3^k))^r := by rw [hpow]
            _ = 2^j := by rw [←Nat.pow_mul, ←hr]
            _ = 1+3^((k+1)+1)*m := hm
        obtain ⟨s,hs⟩ := (pow_lift_iff (k+1) (Q k) r (by omega) hQ).mp ⟨m,hbase⟩
        refine ⟨s, ?_⟩
        calc
          j = (2*3^k)*r := hr
          _ = 2*3^(k+1)*s := by rw [hs,Nat.pow_succ]; ac_rfl
      · rintro ⟨r,hr⟩
        have hbase : 2^j = (1+3^(k+1)*Q k)^(3*r) := by
          calc
            2^j = 2^((2*3^k)*(3*r)) := by
              apply congrArg (fun e : Nat => 2^e)
              rw [hr,Nat.pow_succ]
              ac_rfl
            _ = (2^(2*3^k))^(3*r) := by rw [Nat.pow_mul]
            _ = (1+3^(k+1)*Q k)^(3*r) := by rw [hpow]
        obtain ⟨m,hm⟩ := (pow_lift_iff (k+1) (Q k) (3*r) (by omega) hQ).mpr ⟨r,by ac_rfl⟩
        refine ⟨m, ?_⟩
        rw [hbase]
        exact hm

#print axioms power_cong_iff_exponent
end BB6.Agent39Three

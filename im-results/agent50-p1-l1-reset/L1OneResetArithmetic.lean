import Init.Omega

namespace BB6.Agent50L1OneReset

private theorem dyadic_small_difference
  (n p B K R : Nat)
  (hK : 0 < K) (hsmall : K < 2^p)
  (hsum : B+K=R) (hR : 2^p ∣ R) (hB : 2^n ∣ B) :
  n < p ∧ 2^n ≤ K := by
  have key (j:Nat) (hjB:2^j ∣ B) (hjR:2^j ∣ R) : 2^j ∣ K := by
    have hsumdiv : 2^j ∣ B+K := by rw [hsum]; exact hjR
    exact (Nat.dvd_add_iff_right hjB).mpr hsumdiv
  by_cases hn : p ≤ n
  · have hdB : 2^p ∣ B := Nat.dvd_trans (Nat.pow_dvd_pow 2 hn) hB
    have hdK := key p hdB hR
    have hl := Nat.le_of_dvd hK hdK
    omega
  · have hnp : n < p := by omega
    have hdR : 2^n ∣ R := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hR
    have hdK := key n hB hdR
    exact ⟨hnp, Nat.le_of_dvd hK hdK⟩

/-- Any direct L1 root positive-depth inverse, plus any upper tail,
    misses the affine low-cost wall when the authentic first depth obeys
    its root valuation bound. -/
theorem no_one_reset_l1_budget
    (q t n P0 B K : Nat)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (htop : t ≤ 16*q)
    (hsmallt : 2^t ≤ 20*q+8)
    (hP0 : P0=2^(16*q-t))
    (hK : 0<K) (hKmax : K ≤ 64*q+12)
    (hBalance : B+K+35*P0=56*2^(16*q))
    (hWall : B=2^n*(4*(t+1+n)+64*q+28))
    (hpower : 65536*q*q ≤ 2^(16*q)) : False := by
  let P := 2^(16*q)
  let X := 2^t
  let p := 16*q-t
  let Q := 2^p
  have hp0 : 0<P0 := by simp [hP0]; exact Nat.two_pow_pos _
  have hxp : 0<X := Nat.two_pow_pos _
  have hP : P=X*P0 := by
    dsimp [P,X]
    rw [hP0, ←Nat.pow_add]
    congr 1
    omega
  have hqp : Q=P0 := by simp [Q,p,hP0]
  have hqsmall : q≤q*q := by
    have hh:=Nat.mul_le_mul_right q hq
    omega
  have hKlinear : K≤76*q := by omega
  have ht_linear : X≤28*q := by dsimp [X] at *; omega
  have hsqBound : X*K≤2128*(q*q) := by
    calc
      X*K ≤ (28*q)*(76*q) := Nat.mul_le_mul ht_linear hKlinear
      _ = (28*76)*(q*q) := by ac_rfl
      _ = 2128*(q*q) := by rw [show 28*76=2128 by decide]
  have hPbound : 65536*(q*q)≤P := by
    calc
      65536*(q*q)=65536*q*q := by ac_rfl
      _≤P := hpower
  have hprod : X*K<P := by omega
  have hP0big : K<P0 := by
    have hXK : X*K<X*P0 := by rw [←hP]; exact hprod
    exact Nat.lt_of_mul_lt_mul_left hXK
  have hKQ : K<Q := by rw [hqp]; exact hP0big
  have hdivB : 2^n ∣ B := by
    rw [hWall]
    exact ⟨4*(t+1+n)+64*q+28,rfl⟩
  have hdivR : Q∣B+K := by
    have hdivRight : Q∣35*P0 := by
      rw [hqp]
      refine ⟨35,?_⟩
      omega
    have hdivWhole : Q∣56*P := by
      rw [hqp,hP]
      refine ⟨56*X,?_⟩
      ac_rfl
    apply (Nat.dvd_add_iff_left hdivRight).mpr
    rw [show B+K+35*P0=56*P by exact hBalance]
    exact hdivWhole
  have hdy := dyadic_small_difference n p B K (B+K) hK hKQ rfl
    (by simpa only [Q] using hdivR) hdivB
  have hn : n<p := hdy.1
  have hboundn : 2^n≤76*q := by omega
  have hnbound : n≤16*q := by dsimp [p] at hn; omega
  have hC : 4*(t+1+n)+64*q+28≤224*q := by omega
  have hBupper : B≤17024*(q*q) := by
    calc
      B = 2^n*(4*(t+1+n)+64*q+28) := hWall
      _ ≤ (76*q)*(224*q) := Nat.mul_le_mul hboundn hC
      _ = (76*224)*(q*q) := by ac_rfl
      _=17024*(q*q) := by rw [show 76*224=17024 by decide]
  have h2p : 2*P0≤P := by
    rw [hP]
    exact Nat.mul_le_mul_right P0 (by
      have hh : 2≤2^t := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht
      simpa [X] using hh)
  have h35p : 35*P0≤18*P := by omega
  have hBbig : 38*P≤B+K := by omega
  have hscale := Nat.mul_le_mul_left 38 hPbound
  have hpp : 2490368*(q*q) ≤38*P := by
    calc
      2490368*(q*q)=(38*65536)*(q*q) := by rw [show 38*65536=2490368 by decide]
      _=38*(65536*(q*q)) := by ac_rfl
      _≤38*P := hscale
  omega

#print axioms no_one_reset_l1_budget
end BB6.Agent50L1OneReset

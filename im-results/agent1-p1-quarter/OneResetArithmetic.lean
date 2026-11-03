import DyadicDiff

namespace BB6.Agent1OneReset
open BB6.Agent1RootWall

/-- One positive-depth reset bracketed by any number of upper inversions
    cannot meet the L0 feeder wall once its authentic shifted output gives
    the small first-depth 2-adic bound. Pure arithmetic consumer lemma. -/
theorem no_one_reset_l0_budget
    (q t n P0 B K : Nat)
    (hq : 1≤q) (ht : 1≤t) (htop : t≤16*q)
    (hsmallt : 2^t≤24*q+8)
    (hP0 : P0=2^(16*q-t))
    (hK : 0<K) (hKmax : K≤64*q+10)
    (hBalance : B+K+42*P0=56*2^(16*q))
    (hWall : B=2^n*(4*(t+1+n)+64*q+24)) : False := by
  let P := 2^(16*q)
  let X := 2^t
  let p := 16*q-t+1
  let Q := 2^p
  have hp0 : 0<P0 := by simp [hP0]; exact Nat.two_pow_pos _
  have hxp : 0<X := Nat.two_pow_pos _
  have hP : P=X*P0 := by
    dsimp [P,X]
    rw [hP0, ← Nat.pow_add]
    congr 1
    omega
  have hqp : Q=2*P0 := by
    dsimp [Q,p]
    rw [show 16*q-t+1=(16*q-t)+1 by omega, Nat.pow_succ]
    rw [hP0]
    omega
  have hqsmall : q≤q*q := by
    have hh:=Nat.mul_le_mul_right q hq
    omega
  have hpbound : 65536*q*q≤P := large_power q hq
  have hKlinear : K≤74*q := by omega
  have ht_linear : X≤32*q := by omega
  have hsqBound : X*K≤2368*(q*q) := by
    calc
      X*K ≤ (32*q)*(74*q) := Nat.mul_le_mul ht_linear hKlinear
      _ = (32*74)*(q*q) := by ac_rfl
      _ = 2368*(q*q) := by rw [show 32*74=2368 by decide]
  have hPbound : 65536*(q*q)≤P := by
    calc
      65536*(q*q)=65536*q*q := by ac_rfl
      _≤P := hpbound
  have hprod : X*K <P := by omega
  have hP0big : K<P0 := by
    have hXK : X*K<X*P0 := by rw [←hP]; exact hprod
    exact Nat.lt_of_mul_lt_mul_left hXK
  have hKQ : K<Q := by rw [hqp]; omega
  have hdivB : 2^n ∣ B := by
    rw [hWall]
    exact ⟨4*(t+1+n)+64*q+24,rfl⟩
  have hdivR : Q∣B+K := by
    have hdivRight : Q∣42*P0 := by
      rw [hqp]
      refine ⟨21,?_⟩
      omega
    have hdivWhole : Q∣56*P := by
      rw [hqp,hP]
      refine ⟨28*X,?_⟩
      ac_rfl
    apply (Nat.dvd_add_iff_left hdivRight).mpr
    rw [show B+K+42*P0=56*P by exact hBalance]
    exact hdivWhole
  have hdy := dyadic_small_difference n p B K (B+K) hK hKQ rfl
    (by simpa only [Q] using hdivR) hdivB
  have hn : n<p := hdy.1
  have hboundn : 2^n≤74*q := by omega
  have hnbound : n≤16*q := by dsimp [p] at hn; omega
  have hC : 4*(t+1+n)+64*q+24≤220*q := by omega
  have hBupper : B≤16280*(q*q) := by
    calc
      B = 2^n*(4*(t+1+n)+64*q+24) := hWall
      _ ≤ (74*q)*(220*q) := Nat.mul_le_mul hboundn hC
      _ = (74*220)*(q*q) := by ac_rfl
      _ =16280*(q*q) := by rw [show 74*220=16280 by decide]
  have h2p : 2*P0≤P := by
    rw [hP]
    exact Nat.mul_le_mul_right P0 (by
      have hh : 2≤2^t := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht
      simpa [X] using hh)
  have h42p : 42*P0≤21*P := by omega
  have hBbig : 35*P≤B+K := by omega
  have hscale := Nat.mul_le_mul_left 35 hpbound
  have hpp : 2293760*(q*q) ≤35*P := by
    have hh:35*(65536*q*q)=2293760*(q*q) := by
      calc
        35*(65536*q*q)=(35*65536)*(q*q) := by ac_rfl
        _=2293760*(q*q) := by rw [show 35*65536=2293760 by decide]
    exact hh ▸ hscale
  omega

#print axioms no_one_reset_l0_budget
end BB6.Agent1OneReset

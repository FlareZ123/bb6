import Init.Omega

namespace BB6.Agent50L1All

/-- A uniform fourth-power lower bound, sufficient for the complete single-reset cone. -/
theorem huge_power4 (q : Nat) (hq : 1 ≤ q) :
    65536*q*q*q*q ≤ 2^(16*q) := by
  induction q with
  | zero => omega
  | succ q ih =>
    by_cases hzero : q=0
    · subst q
      decide
    have hq : 1≤q := by omega
    have hi:=ih hq
    have htwo : q+1≤2*q := by omega
    have hsq := Nat.mul_le_mul htwo htwo
    have hquart :
        (q+1)*(q+1)*(q+1)*(q+1) ≤ 16*(q*q*q*q) := by
      calc
        (q+1)*(q+1)*(q+1)*(q+1) = ((q+1)*(q+1))*((q+1)*(q+1)) := by ac_rfl
        _ ≤ ((2*q)*(2*q))*((2*q)*(2*q)) := Nat.mul_le_mul hsq hsq
        _ = 16*(q*q*q*q) := by ac_rfl
    have hp : 2^(16*(q+1)) = 65536*2^(16*q) := by
      rw [show 16*(q+1)=16*q+16 by omega, Nat.pow_add]
      simp [show (2:Nat)^16=65536 by decide, Nat.mul_comm]
    rw [hp]
    have hscaled := Nat.mul_le_mul_left 65536 hquart
    have hscaled2 : 65536*(16*(q*q*q*q)) ≤ 65536*(65536*(q*q*q*q)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_right
      decide
    have hmul := Nat.mul_le_mul_left 65536 hi
    have hfinal : 65536*((q+1)*(q+1)*(q+1)*(q+1)) ≤ 65536*2^(16*q) :=
      Nat.le_trans hscaled (Nat.le_trans hscaled2 (by simpa only [Nat.mul_assoc] using hmul))
    calc
      65536*(q+1)*(q+1)*(q+1)*(q+1) = 65536*((q+1)*(q+1)*(q+1)*(q+1)) := by ac_rfl
      _ ≤ 65536*2^(16*q) := hfinal

theorem dyadic_residue_bound (a p V J C : Nat)
  (hJ : J < 2^p) (hV : V%2=1)
  (heq : 2^a*(C+3)+J=V*2^p) : a≤p := by
  by_cases hle : a≤p
  · exact hle
  have ha : p+1≤a := by omega
  let P := 2^p
  have hp : 0<P := Nat.two_pow_pos _
  have hP2 : 0<2*P := by omega
  have hbig : 2*P ∣ 2^a := by
    have hh := Nat.pow_dvd_pow 2 ha
    simpa only [P,Nat.pow_succ,Nat.mul_comm] using hh
  have hbigProd : 2*P ∣ 2^a*(C+3) := by
    obtain ⟨k,hk⟩ := hbig
    refine ⟨k*(C+3),?_⟩
    rw [hk]
    ac_rfl
  have hmodL : (2^a*(C+3)+J)%(2*P)=J := by
    have hm : (2^a*(C+3))%(2*P)=0 := Nat.dvd_iff_mod_eq_zero.mp hbigProd
    rw [Nat.add_mod,hm]
    have hJl : J<2*P := by dsimp [P] at hJ ⊢; omega
    simp [Nat.mod_eq_of_lt hJl]
  have hVform : V=2*(V/2)+1 := by omega
  have hVmul : (2*(V/2)+1)*P=(2*P)*(V/2)+P := by
    calc
      (2*(V/2)+1)*P=(2*(V/2))*P+P := by rw [Nat.add_mul]; omega
      _=(2*P)*(V/2)+P := by ac_rfl
  have hmodR : (V*P)%(2*P)=P := by
    rw [hVform,hVmul,Nat.add_mod]
    have h1 : ((2*P)*(V/2))%(2*P)=0 := by
      apply Nat.dvd_iff_mod_eq_zero.mp
      exact ⟨V/2,rfl⟩
    rw [h1]
    have hPl : P<2*P := by omega
    simp [Nat.mod_eq_of_lt hPl]
  have hmodEq := congrArg (fun z:Nat => z%(2*P)) heq
  rw [hmodL,hmodR] at hmodEq
  omega

theorem dyadic_small_difference
  (n p B K R:Nat)
  (hK:0<K) (hsmall:K<2^p)
  (hsum:B+K=R)
  (hR:2^p∣R)
  (hB:2^n∣B) : n<p ∧ 2^n≤K := by
  have key (j:Nat) (hjB:2^j∣B) (hjR:2^j∣R) : 2^j∣K := by
    have hsumdiv:2^j∣B+K := by rw [hsum]; exact hjR
    exact (Nat.dvd_add_iff_right hjB).mpr hsumdiv
  by_cases hn:p≤n
  · have hdB:2^p∣B := Nat.dvd_trans (Nat.pow_dvd_pow 2 hn) hB
    have hdK := key p hdB hR
    have hl := Nat.le_of_dvd hK hdK
    omega
  · have hnp:n<p := by omega
    have hdR:2^n∣R := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hR
    have hdK := key n hB hdR
    exact ⟨hnp,Nat.le_of_dvd hK hdK⟩

/-- All-q arithmetic obstruction for an L1 upper prefix, one positive reset,
    and any upper suffix, provided the exact source-derived equations hold. -/
theorem all_prefix_one_reset_obstruction
    (q r t n X Y P V J C B : Nat)
    (hq : 1≤q) (ht : 1≤t)
    (hX : X=2^r) (hY : Y=2^t) (hP : P=2^(16*q))
    (hXsmall : X≤6*q+2) (hr : r≤16*q)
    (hJdef : J+12*q+4=(32*q+12+2*r)*X)
    (hVdef : V+21=56*X)
    (hJpos : 0<J) (hJsmall : J<P)
    (hsource : X*Y*(C+3)+J=V*P)
    (hpost : B+C+3+32*q+12+2*r+2*t=56*P)
    (hwall : B=2^n*(4*(r+t+1+n)+64*q+28)) : False := by
  let Z := 2^(r+t)
  have hZeq : Z=X*Y := by
    dsimp [Z]
    rw [Nat.pow_add,hX,hY]
  have hXpos : 0<X := by rw [hX]; exact Nat.two_pow_pos _
  have hYlow : 2≤Y := by
    rw [hY]
    have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht
    simpa using hh
  have hVodd : V%2=1 := by omega
  have hsource' : Z*(C+3)+J=V*P := by rw [hZeq]; simpa only [Nat.mul_assoc] using hsource
  have hsum : r+t≤16*q := by
    apply dyadic_residue_bound (r+t) (16*q) V J C
    · simpa [hP] using hJsmall
    · exact hVodd
    · simpa [Z,hP] using hsource'
  have hZdivP : Z∣P := by
    rw [hP]
    exact Nat.pow_dvd_pow 2 hsum
  obtain ⟨Q,hPfact⟩ := hZdivP
  have hZpos : 0<Z := by dsimp [Z]; exact Nat.two_pow_pos _
  have hQpos : 0<Q := by
    have hPpos : 0<P := by rw [hP]; exact Nat.two_pow_pos _
    by_cases hzero : Q=0
    · have hpzero : P=0 := by rw [hPfact,hzero]; simp
      omega
    · omega
  have hZdivVP : Z∣V*P := by
    rw [hPfact]
    refine ⟨V*Q,?_⟩
    ac_rfl
  have hZdivZC : Z∣Z*(C+3) := ⟨C+3,rfl⟩
  have hZdivJ : Z∣J := by
    apply (Nat.dvd_add_iff_right hZdivZC).mpr
    rw [hsource']
    exact hZdivVP
  obtain ⟨H,hJfact⟩ := hZdivJ
  have hZltJ : Z≤J := Nat.le_of_dvd hJpos ⟨H,hJfact⟩
  let S := 32*q+12+2*r
  have hSbound : S≤76*q := by dsimp [S]; omega
  have hXbound : X≤8*q := by omega
  have hJbound : J≤S*X := by dsimp [S]; omega
  have hZbound : Z≤608*(q*q) := by
    calc
      Z ≤ J := hZltJ
      _ ≤ S*X := hJbound
      _ ≤ (76*q)*(8*q) := Nat.mul_le_mul hSbound hXbound
      _ = 608*(q*q) := by ac_rfl
  have hHrelation : C+3+H=V*Q := by
    have hc : Z*(C+3+H)=Z*(V*Q) := by
      calc
        Z*(C+3+H)=Z*(C+3)+Z*H := by rw [Nat.mul_add]
        _=V*P := by omega
        _=Z*(V*Q) := by rw [hPfact]; ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hZpos hc
  have hSY : Y*H ≤ S := by
    have heq : X*(Y*H)+12*q+4=S*X := by
      calc
        X*(Y*H)+12*q+4 = J+12*q+4 := by rw [hJfact,hZeq]; ac_rfl
        _=S*X := by simpa [S] using hJdef
    have hsml : X*(Y*H)≤ X*S := by
      have heqRight : X*(Y*H)+12*q+4=X*S := by
        calc
          _=S*X := heq
          _=X*S := by ac_rfl
      omega
    have heq' : X*(Y*H)≤X*S := by simpa [Nat.mul_comm] using hsml
    exact Nat.le_of_mul_le_mul_left heq' hXpos
  have hHsmall : 2*H≤S := by
    have hh := Nat.mul_le_mul_right H hYlow
    omega
  let K := S+2*t-H
  have hKsum : K+H=S+2*t := by dsimp [K]; omega
  have hKpos : 0<K := by dsimp [K]; omega
  have hKbound : K≤76*q := by
    have hSt : S+2*t≤76*q := by dsimp [S]; omega
    omega
  have hbalance : B+K+V*Q=56*P := by omega
  have hQdivP : Q ∣ P := by rw [hPfact]; exact ⟨Z,by ac_rfl⟩
  have hQdivV : Q∣V*Q := ⟨V,by ac_rfl⟩
  have hQdivB : Q∣B+K := by
    apply (Nat.dvd_add_iff_left hQdivV).mpr
    rw [hbalance]
    obtain ⟨w,hw⟩ := hQdivP
    refine ⟨56*w,?_⟩
    rw [hw]
    ac_rfl
  have hPbound : 65536*q*q*q*q≤P := by
    rw [hP]
    exact huge_power4 q hq
  have hq3q4 : q*q*q≤q*q*q*q := by
    calc
      q*q*q=(q*q*q)*1 := by simp
      _ ≤ (q*q*q)*q := Nat.mul_le_mul_left (q*q*q) hq
      _ = q*q*q*q := by ac_rfl
  have hKprod : Z*K≤46208*(q*q*q) := by
    calc
      Z*K ≤ (608*(q*q))*(76*q) := Nat.mul_le_mul hZbound hKbound
      _ = 46208*(q*q*q) := by ac_rfl
  have hPcompare : Z*K<P := by
    have h1 := Nat.mul_le_mul_left 46208 hq3q4
    have h2 : 46208*(q*q*q*q) <65536*(q*q*q*q) := by
      have hq4pos : 0<q*q*q*q := by
        have hh : 0<q := by omega
        exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hh hh) hh) hh
      have ht := Nat.mul_lt_mul_of_pos_right (by decide : 46208<65536) hq4pos
      exact ht
    have hPboundEq : 65536*(q*q*q*q)≤P := by simpa only [Nat.mul_assoc] using hPbound
    omega
  have hKltQ : K<Q := by
    have hh : Z*K<Z*Q := by rw [←hPfact]; exact hPcompare
    exact Nat.lt_of_mul_lt_mul_left hh
  have hQpow : Q=2^(16*q-(r+t)) := by
    have hh : Z*2^(16*q-(r+t))=P := by
      dsimp [Z]
      rw [hP,←Nat.pow_add]
      congr 1
      omega
    rw [hPfact] at hh
    exact Nat.eq_of_mul_eq_mul_left hZpos hh.symm
  have hBdiv : 2^n∣B := by
    rw [hwall]
    exact ⟨4*(r+t+1+n)+64*q+28,rfl⟩
  have hdy : n<16*q-(r+t) ∧ 2^n≤K :=
    dyadic_small_difference n (16*q-(r+t)) B K (B+K)
      hKpos (by rw [←hQpow]; exact hKltQ) rfl
      (by rw [←hQpow]; exact hQdivB) hBdiv
  have hnbound : n≤16*q := by omega
  have hN : 2^n≤76*q := by omega
  have hCbound : 4*(r+t+1+n)+64*q+28≤224*q := by omega
  have hBbound : B≤17024*(q*q) := by
    calc
      B = 2^n*(4*(r+t+1+n)+64*q+28) := hwall
      _ ≤ (76*q)*(224*q) := Nat.mul_le_mul hN hCbound
      _ = 17024*(q*q) := by ac_rfl
  have hVbound : V≤56*X := by omega
  have hVQbound : V*Q≤28*P := by
    calc
      V*Q≤(56*X)*Q := Nat.mul_le_mul_right Q hVbound
      _ = (28*X)*(2*Q) := by ac_rfl
      _ ≤ (28*X)*(Y*Q) := Nat.mul_le_mul_left (28*X) (Nat.mul_le_mul_right Q hYlow)
      _ = 28*P := by rw [hPfact,hZeq]; ac_rfl
  have hBbig : 28*P≤B+K := by omega
  have hQsq : q*q≤q*q*q*q := by
    have hsqpos : 1≤q*q := by
      have hh : 0<q := by omega
      have hpos := Nat.mul_pos hh hh
      omega
    calc
      q*q=(q*q)*1 := by simp
      _ ≤ (q*q)*(q*q) := Nat.mul_le_mul_left (q*q) hsqpos
      _ = q*q*q*q := by ac_rfl
  have hcontr : (17024*(q*q))+76*q <28*P := by
    have hqle : q≤q*q := by
      have hh := Nat.mul_le_mul_right q hq
      omega
    have hfirst : 17024*(q*q)+76*q≤17100*(q*q) := by omega
    have hsecond := Nat.mul_le_mul_left 17100 hQsq
    have hq4pos : 0<q*q*q*q :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega : 0<q) (by omega : 0<q)) (by omega : 0<q)) (by omega : 0<q)
    have hthird : 17100*(q*q*q*q)<(28*65536)*(q*q*q*q) :=
      Nat.mul_lt_mul_of_pos_right (by decide) hq4pos
    have hfourth : (28*65536)*(q*q*q*q)≤28*P := by
      have hpow : 65536*(q*q*q*q)≤P := by simpa only [Nat.mul_assoc] using hPbound
      have hh:=Nat.mul_le_mul_left 28 hpow
      simpa only [Nat.mul_assoc] using hh
    calc
      17024*(q*q)+76*q ≤ 17100*(q*q) := hfirst
      _ ≤ 17100*(q*q*q*q) := hsecond
      _ < (28*65536)*(q*q*q*q) := hthird
      _ ≤ 28*P := hfourth
  omega

#print axioms all_prefix_one_reset_obstruction
end BB6.Agent50L1All

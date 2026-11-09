import Std

namespace SheepSpecialDepth

/-- At the exceptional source exponent, the additive offset is smaller than
    its dyadic scale. -/
private theorem tiny_offset (a : Nat) (ha : 5 ≤ a) : a+15 < 2^a := by
  have aux : ∀ t : Nat, (t+5)+15 < 2^(t+5) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      have hpow : 2^(t+1+5) = 2^(t+5)*2 := by
        rw [show t+1+5=t+5+1 by omega, Nat.pow_succ]
      rw [hpow]
      omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le ha
  subst a
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using aux t

/-- Uniform bound. The odd coefficient M may depend on depth n. -/
theorem no_deep_special
    {M a n b s u : Nat}
    (hM : Nat.Coprime M 2)
    (hs : a ≤ s)
    (ha : 5 ≤ a)
    (heq : M*(3*2^a+a+15) = 8^n*(2^s+2^b*u)) :
    3*n+b < a ∧ 2^(3*n+b) ∣ a+15 := by
  let t := min a (3*n+b)
  have hta : t ≤ a := Nat.min_le_left _ _
  have htn : t ≤ 3*n+b := Nat.min_le_right _ _
  have hpowa : 2^t ∣ 2^a := Nat.pow_dvd_pow 2 hta
  have hpowS : 2^t ∣ 2^s := Nat.pow_dvd_pow 2 (by omega)
  have hpowB : 2^t ∣ 2^(3*n+b) := Nat.pow_dvd_pow 2 htn
  have hpow8 : 8^n = 2^(3*n) := by
    change (2^3)^n = 2^(3*n)
    rw [Nat.pow_mul]
  have hpowR : 8^n*(2^s+2^b*u) =
      2^(3*n+s)+2^(3*n+b)*u := by
    rw [hpow8, Nat.mul_add, Nat.pow_add, Nat.pow_add]
    ac_rfl
  have hright : 2^t ∣ 8^n*(2^s+2^b*u) := by
    rw [hpowR]
    have hd1 : 2^t ∣ 2^(3*n+s) := Nat.pow_dvd_pow 2 (by omega)
    have hd2 : 2^t ∣ 2^(3*n+b)*u := by
      obtain ⟨w,hw⟩ := hpowB
      refine ⟨w*u, ?_⟩
      rw [hw]
      ac_rfl
    exact Nat.dvd_add hd1 hd2
  have hleft : 2^t ∣ M*(3*2^a) := by
    obtain ⟨w, hw⟩ := hpowa
    refine ⟨M*3*w, ?_⟩
    rw [hw]
    ac_rfl
  have hwhole : 2^t ∣ M*(3*2^a)+M*(a+15) := by
    have heq2 : M*(3*2^a)+M*(a+15) = 8^n*(2^s+2^b*u) := by
      rw [←Nat.mul_add]
      simpa [Nat.add_assoc] using heq
    rw [heq2]
    exact hright
  have hpart : 2^t ∣ M*(a+15) :=
    (Nat.dvd_add_iff_right hleft).mpr hwhole
  have hcop : Nat.Coprime (2^t) M := (hM.symm.pow_left t)
  have hdiv : 2^t ∣ a+15 := hcop.dvd_of_dvd_mul_left hpart
  have hstrict : 3*n+b < a := by
    by_cases hh : 3*n+b < a
    · exact hh
    have ht : t=a := Nat.min_eq_left (by omega)
    have hd : 2^a ∣ a+15 := ht ▸ hdiv
    have hle : 2^a ≤ a+15 := Nat.le_of_dvd (by omega) hd
    have hsz := tiny_offset a ha
    omega
  refine ⟨hstrict, ?_⟩
  have ht : t=3*n+b := Nat.min_eq_right (by omega)
  exact ht ▸ hdiv

/-- Odd M at least 8^n gives an unconditional logarithmic depth cutoff. -/
theorem special_depth_cutoff
    {M a n b s u : Nat}
    (hM : Nat.Coprime M 2)
    (hlarge : 8^n ≤ M)
    (hC : 2^b*u < 2^s)
    (ha : 5 ≤ a)
    (heq : M*(3*2^a+a+15) = 8^n*(2^s+2^b*u)) :
    3*n+b < a ∧ 2^(3*n+b) < s+15 := by
  have hp : 0<8^n := Nat.pow_pos (by decide)
  have hprod : 8^n*(3*2^a+a+15) ≤ 8^n*(2^s+2^b*u) := by
    calc
      _ ≤ M*(3*2^a+a+15) := Nat.mul_le_mul_right _ hlarge
      _ = _ := heq
  have hbase := Nat.le_of_mul_le_mul_left hprod hp
  have has : a<s := by
    by_cases h : a<s
    · exact h
    have hpow : 2^s ≤ 2^a := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨hdepth, hdvd⟩ := no_deep_special hM (by omega) ha heq
  have hsmall : 2^(3*n+b) ≤ a+15 := Nat.le_of_dvd (by omega) hdvd
  exact ⟨hdepth, by omega⟩

/-- Z terminal: all exceptional h=0 sources obey 2^(3n+2) < j+25. -/
theorem z_special_depth_bound
    {j n a : Nat}
    (hj : 10 ≤ j)
    (ha : 5 ≤ a)
    (heq : (3483*9^n)*(3*2^a+a+15) =
      8^n*(2^(j+10)+25220)) :
    3*n+2 < a ∧ 2^(3*n+2) < j+25 := by
  have hcop : Nat.Coprime (3483*9^n) 2 :=
    (show Nat.Coprime 3483 2 by decide).mul_left
      ((show Nat.Coprime 9 2 by decide).pow_left n)
  have hbig : 8^n ≤ 3483*9^n := by
    have h89 : 8^n ≤ 9^n := Nat.pow_le_pow_left (by decide) n
    omega
  have hlimit : 2^2*6305 < 2^(j+10) := by
    have hpow : 2^20 ≤ 2^(j+10) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have heq2 : (3483*9^n)*(3*2^a+a+15) =
      8^n*(2^(j+10)+2^2*6305) := by
    simpa using heq
  have h := special_depth_cutoff hcop hbig hlimit ha heq2
  simpa [Nat.add_assoc] using h

/-- Seven X corridors obey 2^(3n+3) < j+26. -/
theorem x_special_depth_bound
    {j n a : Nat}
    (hj : 10 ≤ j)
    (ha : 5 ≤ a)
    (heq : (59049*9^n)*(3*2^a+a+15) =
      8^n*(2^(j+11)+680296)) :
    3*n+3 < a ∧ 2^(3*n+3) < j+26 := by
  have hcop : Nat.Coprime (59049*9^n) 2 :=
    (show Nat.Coprime 59049 2 by decide).mul_left
      ((show Nat.Coprime 9 2 by decide).pow_left n)
  have hbig : 8^n ≤ 59049*9^n := by
    have h89 : 8^n ≤ 9^n := Nat.pow_le_pow_left (by decide) n
    omega
  have hlimit : 2^3*85037 < 2^(j+11) := by
    have hpow : 2^21 ≤ 2^(j+11) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have heq2 : (59049*9^n)*(3*2^a+a+15) =
      8^n*(2^(j+11)+2^3*85037) := by
    simpa using heq
  have h := special_depth_cutoff hcop hbig hlimit ha heq2
  simpa [Nat.add_assoc] using h

private theorem special_a_at_least_five
    {x a : Nat}
    (hshape : x%8=0 ∨ x%8=4)
    (hspecial : x=3*2^a+a+3) : 5 ≤ a := by
  by_cases ha : 5 ≤ a
  · exact ha
  have cases : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 := by omega
  rcases cases with h0 | h1 | h2 | h3 | h4
  all_goals subst a; simp at hspecial; omega

/-- Source-compatible P-chain and exact Z parent imply the depth cutoff. -/
theorem z_from_chain
    {j n x y a : Nat}
    (hj : 10 ≤ j)
    (hx : x%8=0 ∨ x%8=4)
    (hchain : 9^n*(x+12)=8^n*(y+12))
    (hterminal : 3483*(y+12)=2^(j+10)+25220)
    (hspecial : x=3*2^a+a+3) :
    3*n+2 < a ∧ 2^(3*n+2) < j+25 := by
  have ha := special_a_at_least_five hx hspecial
  have hxe : x+12 = 3*2^a+a+15 := by omega
  have heq : (3483*9^n)*(3*2^a+a+15) = 8^n*(2^(j+10)+25220) := by
    calc
      _ = 3483*(9^n*(x+12)) := by rw [hxe]; ac_rfl
      _ = 3483*(8^n*(y+12)) := by rw [hchain]
      _ = 8^n*(3483*(y+12)) := by ac_rfl
      _ = 8^n*(2^(j+10)+25220) := by rw [hterminal]
  exact z_special_depth_bound hj ha heq

/-- Source-compatible P-chain and exact X parent imply the depth cutoff. -/
theorem x_from_chain
    {j n x y a : Nat}
    (hj : 10 ≤ j)
    (hx : x%8=0 ∨ x%8=4)
    (hchain : 9^n*(x+12)=8^n*(y+12))
    (hterminal : 59049*(y+12)=2^(j+11)+680296)
    (hspecial : x=3*2^a+a+3) :
    3*n+3 < a ∧ 2^(3*n+3) < j+26 := by
  have ha := special_a_at_least_five hx hspecial
  have hxe : x+12 = 3*2^a+a+15 := by omega
  have heq : (59049*9^n)*(3*2^a+a+15) = 8^n*(2^(j+11)+680296) := by
    calc
      _ = 59049*(9^n*(x+12)) := by rw [hxe]; ac_rfl
      _ = 59049*(8^n*(y+12)) := by rw [hchain]
      _ = 8^n*(59049*(y+12)) := by ac_rfl
      _ = 8^n*(2^(j+11)+680296) := by rw [hterminal]
  exact x_special_depth_bound hj ha heq

/-- Z deep region has no exceptional cofactor-three h=0 source. -/
theorem z_no_special_deep
    {j n x y a : Nat}
    (hj : 10 ≤ j)
    (hx : x%8=0 ∨ x%8=4)
    (hchain : 9^n*(x+12)=8^n*(y+12))
    (hterminal : 3483*(y+12)=2^(j+10)+25220)
    (hdepth : j+25 ≤ 2^(3*n+2))
    (hspecial : x=3*2^a+a+3) : False := by
  have hc := z_from_chain hj hx hchain hterminal hspecial
  omega

/-- X deep region has no exceptional cofactor-three h=0 source. -/
theorem x_no_special_deep
    {j n x y a : Nat}
    (hj : 10 ≤ j)
    (hx : x%8=0 ∨ x%8=4)
    (hchain : 9^n*(x+12)=8^n*(y+12))
    (hterminal : 59049*(y+12)=2^(j+11)+680296)
    (hdepth : j+26 ≤ 2^(3*n+3))
    (hspecial : x=3*2^a+a+3) : False := by
  have hc := x_from_chain hj hx hchain hterminal hspecial
  omega

private theorem odd_not_double (e u : Nat) (hu : u%2=1) :
    ¬ 2^(e+1) ∣ 2^e*u := by
  intro h
  obtain ⟨w, hw⟩ := h
  have hc : 2^e*u = 2^e*(2*w) := by
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hw
  have he : 0 < 2^e := Nat.pow_pos (by decide)
  have heq : u=2*w := Nat.eq_of_mul_eq_mul_left he hc
  omega

/-- Exact dyadic order of the exceptional source valuation offset. -/
theorem exact_special_dyadic_depth
    {M a n b s u : Nat}
    (hM : Nat.Coprime M 2)
    (hs : a ≤ s)
    (ha : 5 ≤ a)
    (hu : u%2=1)
    (heq : M*(3*2^a+a+15) = 8^n*(2^s+2^b*u)) :
    2^(3*n+b) ∣ a+15 ∧ ¬ 2^(3*n+b+1) ∣ a+15 := by
  obtain ⟨hstrict, hdiv⟩ := no_deep_special hM hs ha heq
  refine ⟨hdiv, ?_⟩
  intro htoo
  let e := 3*n+b
  have hDA : 2^(e+1) ∣ 2^a := Nat.pow_dvd_pow 2 (by dsimp [e]; omega)
  have hDS : 2^(e+1) ∣ 2^(3*n+s) := Nat.pow_dvd_pow 2 (by dsimp [e]; omega)
  have hleft : 2^(e+1) ∣ M*(3*2^a+a+15) := by
    have hpart : 2^(e+1) ∣ 3*2^a + (a+15) := by
      have hd1 : 2^(e+1) ∣ 3*2^a := by
        obtain ⟨w,hw⟩ := hDA
        refine ⟨3*w, ?_⟩
        rw [hw]
        ac_rfl
      exact Nat.dvd_add hd1 htoo
    obtain ⟨w, hw⟩ := hpart
    refine ⟨M*w, ?_⟩
    rw [show 3*2^a+a+15=3*2^a+(a+15) by omega, hw]
    ac_rfl
  have hpow8 : 8^n = 2^(3*n) := by
    change (2^3)^n = 2^(3*n)
    rw [Nat.pow_mul]
  have hrew : 8^n*(2^s+2^b*u) = 2^(3*n+s)+2^e*u := by
    dsimp [e]
    rw [hpow8, Nat.mul_add, Nat.pow_add, Nat.pow_add]
    ac_rfl
  have hsum : 2^(e+1) ∣ 2^(3*n+s)+2^e*u := by
    rw [←hrew, ←heq]
    exact hleft
  have hlast : 2^(e+1) ∣ 2^e*u :=
    (Nat.dvd_add_iff_right hDS).mpr hsum
  exact odd_not_double e u hu hlast


/-- For all s>=100, a fixed 2^38 constant times a fifth-degree
    polynomial is dominated by 2^s; proof uses only division by ten. -/
theorem exponential_beats_quintic (s : Nat) (hs : 100 ≤ s) :
    2^38*(s+15)^5 ≤ 2^s := by
  have aux : ∀ w : Nat, 10*(w+10)+24 ≤ 2^(w+10) := by
    intro w
    induction w with
    | zero => decide
    | succ w ih =>
      have hpow : 2^(w+1+10)=2^(w+10)*2 := by
        rw [show w+1+10=w+10+1 by omega, Nat.pow_succ]
      rw [hpow]
      omega
  let t := s/10
  have ht : 10 ≤ t := by dsimp [t]; omega
  have hr : s%10 < 10 := Nat.mod_lt s (by decide)
  have hrepr : s = 10*t + s%10 := by dsimp [t]; omega
  have hb : s+15 ≤ 2^t := by
    have hbase := aux (t-10)
    have hteq : t-10+10=t := by omega
    rw [hteq] at hbase
    omega
  have hp : (s+15)^5 ≤ (2^t)^5 := Nat.pow_le_pow_left hb 5
  have hpp : (2^t)^5 = 2^(5*t) := by
    rw [←Nat.pow_mul]
    congr 1
    omega
  rw [hpp] at hp
  calc
    2^38*(s+15)^5 ≤ 2^38*2^(5*t) := Nat.mul_le_mul_left _ hp
    _ = 2^(38+5*t) := by rw [Nat.pow_add]
    _ ≤ 2^s := Nat.pow_le_pow_right (by decide) (by omega)

/-- Under sufficient size bounds, a dyadic equality forces a forbidden
    equality between an integer divisible by three and one coprime to three. -/
theorem no_special_if_both_small
    {M a n s C : Nat}
    (hs : a ≤ s)
    (hM3 : 3 ∣ M)
    (hC3 : ¬ 3 ∣ C)
    (hA : M*(a+15) < 2^a)
    (hB : 8^n*C < 2^a)
    (heq : M*(3*2^a+a+15) = 8^n*(2^s+C)) : False := by
  have hd1 : 2^a ∣ M*(3*2^a) := by
    refine ⟨M*3, ?_⟩
    ac_rfl
  have hd2 : 2^a ∣ 8^n*2^s := by
    obtain ⟨w,hw⟩ := Nat.pow_dvd_pow 2 hs
    refine ⟨8^n*w, ?_⟩
    rw [hw]
    ac_rfl
  have hsplit : M*(a+15)+M*(3*2^a) =8^n*C+8^n*2^s := by
    calc
      _ = M*(3*2^a+a+15) := by rw [←Nat.mul_add]; congr 1; omega
      _ = 8^n*(2^s+C) := heq
      _ = _ := by rw [Nat.mul_add]; omega
  have hmod : (M*(a+15))%(2^a) = (8^n*C)%(2^a) := by
    have h := congrArg (fun v : Nat => v % (2^a)) hsplit
    simp only [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd1,
      Nat.mod_eq_zero_of_dvd hd2, Nat.add_zero, Nat.mod_mod] at h
    exact h
  have hequal : M*(a+15)=8^n*C := by
    rwa [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB] at hmod
  have hdiv : 3 ∣ 8^n*C := by
    rw [←hequal]
    obtain ⟨w,hw⟩ := hM3
    refine ⟨w*(a+15), ?_⟩
    rw [hw]
    ac_rfl
  have hcop : Nat.Coprime 3 (8^n) :=
    (show Nat.Coprime 3 8 by decide).pow_right n
  exact hC3 (hcop.dvd_of_dvd_mul_left hdiv)

/-- Exponential domination turns a congruence mod 2^a into equality
    for a special source. -/
theorem both_small_from_growth
    {M D C a n s : Nat}
    (hs : 100 ≤ s)
    (ha : 5 ≤ a)
    (hMpos : 0 < M)
    (haS : a ≤ s)
    (hMbound : M ≤ D*(s+15)^2)
    (h8bound : 8^n ≤ s+15)
    (hconst : 4*D*(D+C) ≤ 2^38)
    (heq : M*(3*2^a+a+15) = 8^n*(2^s+C)) :
    M*(a+15)<2^a ∧ 8^n*C<2^a := by
  let B := s+15
  have hBpos : 0<B := by dsimp [B]; omega
  have hBcube : B≤B^3 := by
    simpa using (Nat.pow_le_pow_right hBpos (show 1≤3 by decide))
  have hA_bound : M*(a+15) ≤ (D+C)*B^3 := by
    have hh : M*(a+15) ≤ (D*B^2)*B :=
      Nat.mul_le_mul hMbound (by dsimp [B]; omega)
    have hpow : B^2*B=B^3 := (Nat.pow_succ B 2).symm
    have htmp : (D*B^2)*B ≤ (D+C)*B^3 := by
      calc
        _ = D*B^3 := by rw [←hpow]; ac_rfl
        _ ≤ (D+C)*B^3 := Nat.mul_le_mul_right _ (by omega : D ≤ D+C)
    exact Nat.le_trans hh htmp
  have hB_bound : 8^n*C ≤ (D+C)*B^3 := by
    have hh : 8^n*C ≤ B*C := Nat.mul_le_mul_right _ h8bound
    have htmp : B*C ≤ B^3*(D+C) := by
      exact Nat.mul_le_mul hBcube (by omega : C ≤ D+C)
    simpa [Nat.mul_comm] using (Nat.le_trans hh htmp)
  have hKP : (4*D*B^2)*((D+C)*B^3) ≤ 2^s := by
    calc
      _ = (4*D*(D+C))*B^5 := by
        have hp : B^5=B^2*B^3 := by
          rw [show 5=2+3 by decide, Nat.pow_add]
        rw [hp]
        ac_rfl
      _ ≤ 2^38*B^5 := Nat.mul_le_mul_right _ hconst
      _ ≤ 2^s := exponential_beats_quintic s hs
  have hval : 3*2^a+a+15 < 4*2^a := by
    have hsmall := tiny_offset a ha
    omega
  have hsource : 2^s < (4*D*B^2)*2^a := by
    calc
      2^s ≤ 8^n*2^s := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
      _ ≤ 8^n*(2^s+C) := Nat.mul_le_mul_left _ (by omega)
      _ = M*(3*2^a+a+15) := heq.symm
      _ < M*(4*2^a) := Nat.mul_lt_mul_of_pos_left hval hMpos
      _ ≤ (D*B^2)*(4*2^a) := Nat.mul_le_mul_right _ hMbound
      _ = (4*D*B^2)*2^a := by ac_rfl
  have hP : (D+C)*B^3 < 2^a :=
    Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hKP hsource)
  exact ⟨Nat.lt_of_le_of_lt hA_bound hP, Nat.lt_of_le_of_lt hB_bound hP⟩

/-- Complete absence of special h=0 incoming sources in a corridor whose
    terminal numerator has the stated small odd denominator. -/
theorem no_special_whole_corridor
    {D C b u a n s : Nat}
    (hDpos : 0<D)
    (hDc : Nat.Coprime D 2)
    (hD3 : 3 ∣ D)
    (hC3 : ¬ 3 ∣ C)
    (hCpow : C=2^b*u)
    (hCsmall : C<2^s)
    (hs100 : 100≤s)
    (hK : 4*D*(D+C) ≤ 2^38)
    (ha5 : 5≤a)
    (heq : (D*9^n)*(3*2^a+a+15)=8^n*(2^s+C)) : False := by
  let M := D*9^n
  have hcop : Nat.Coprime M 2 :=
    hDc.mul_left ((show Nat.Coprime 9 2 by decide).pow_left n)
  have hlarge : 8^n ≤ M := by
    have h89 : 8^n≤9^n := Nat.pow_le_pow_left (by decide) n
    have h9pos : 0<9^n := Nat.pow_pos (by decide)
    dsimp [M]
    have hd : 1≤D := hDpos
    have hh : 9^n≤D*9^n := Nat.le_mul_of_pos_left _ hDpos
    omega
  have hMpos :0<M := by
    dsimp [M]
    exact Nat.mul_pos hDpos (Nat.pow_pos (by decide))
  have heq2 : M*(3*2^a+a+15)=8^n*(2^s+2^b*u) := by
    simpa [M,hCpow] using heq
  obtain ⟨hadepth, hcut⟩ := special_depth_cutoff hcop hlarge
    (by simpa [hCpow] using hCsmall) ha5 heq2
  have has : a<s := by
    have hp : 0<8^n := Nat.pow_pos (by decide)
    have hprod : 8^n*(3*2^a+a+15) ≤ 8^n*(2^s+C) := by
      calc
        _ ≤ M*(3*2^a+a+15) := Nat.mul_le_mul_right _ hlarge
        _ = _ := heq
    have hbase := Nat.le_of_mul_le_mul_left hprod hp
    by_cases hh : a<s
    · exact hh
    have hpow : 2^s≤2^a := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let B := s+15
  have h8bound : 8^n ≤ B := by
    have hp : 8^n =2^(3*n) := by
      change (2^3)^n=2^(3*n)
      rw [Nat.pow_mul]
    have hpow : 2^(3*n)≤2^(3*n+b) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    dsimp [B]
    omega
  have h9bound : 9^n ≤ B^2 := by
    have hpow : 9^n≤64^n := Nat.pow_le_pow_left (by decide) n
    have h64 : 64^n = (8^n)^2 := by
      calc
        64^n = (8^2)^n := by rfl
        _ = 8^(2*n) := by rw [Nat.pow_mul]
        _ = 8^(n*2) := by rw [Nat.mul_comm]
        _ = (8^n)^2 := by rw [Nat.pow_mul]
    have hpow2 : (8^n)^2 ≤B^2 := Nat.pow_le_pow_left h8bound 2
    omega
  have hMbound : M≤D*B^2 := by
    dsimp [M]
    exact Nat.mul_le_mul_left _ h9bound
  have hsmall := both_small_from_growth hs100 ha5 hMpos (Nat.le_of_lt has) hMbound h8bound hK heq
  have hm3 : 3∣M := by
    dsimp [M]
    obtain ⟨w,hw⟩ := hD3
    refine ⟨w*9^n, ?_⟩
    rw [hw]
    ac_rfl
  exact no_special_if_both_small (Nat.le_of_lt has) hm3 hC3 hsmall.1 hsmall.2 heq

/-- Complete Z exceptional h=0 branch elimination, for every chain depth
    and every possible cofactor-three source valuation. -/
theorem z_no_special_any_depth
    {j n x y a : Nat}
    (hj : 100 ≤ j)
    (hx : x%8=0 ∨ x%8=4)
    (hchain : 9^n*(x+12)=8^n*(y+12))
    (hterminal : 3483*(y+12)=2^(j+10)+25220)
    (hspecial : x=3*2^a+a+3) : False := by
  have ha := special_a_at_least_five hx hspecial
  have hxe : x+12=3*2^a+a+15 := by omega
  have heq : (3483*9^n)*(3*2^a+a+15)=8^n*(2^(j+10)+25220) := by
    calc
      _ = 3483*(9^n*(x+12)) := by rw [hxe]; ac_rfl
      _ = 3483*(8^n*(y+12)) := by rw [hchain]
      _ = 8^n*(3483*(y+12)) := by ac_rfl
      _ = 8^n*(2^(j+10)+25220) := by rw [hterminal]
  have hCsmall : 25220<2^(j+10) := by
    have hpow : 2^20≤2^(j+10) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  exact no_special_whole_corridor (D:=3483) (C:=25220) (b:=2)
    (u:=6305) (s:=j+10) (a:=a) (n:=n)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hCsmall (by omega) (by decide) ha heq

/-- Complete X exceptional h=0 branch elimination, uniformly across
    the seven h8 mixed terminal families. -/
theorem x_no_special_any_depth
    {j n x y a : Nat}
    (hj : 100 ≤ j)
    (hx : x%8=0 ∨ x%8=4)
    (hchain : 9^n*(x+12)=8^n*(y+12))
    (hterminal : 59049*(y+12)=2^(j+11)+680296)
    (hspecial : x=3*2^a+a+3) : False := by
  have ha := special_a_at_least_five hx hspecial
  have hxe : x+12=3*2^a+a+15 := by omega
  have heq : (59049*9^n)*(3*2^a+a+15)=8^n*(2^(j+11)+680296) := by
    calc
      _ = 59049*(9^n*(x+12)) := by rw [hxe]; ac_rfl
      _ = 59049*(8^n*(y+12)) := by rw [hchain]
      _ = 8^n*(59049*(y+12)) := by ac_rfl
      _ = 8^n*(2^(j+11)+680296) := by rw [hterminal]
  have hCsmall : 680296<2^(j+11) := by
    have hpow : 2^21≤2^(j+11) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  exact no_special_whole_corridor (D:=59049) (C:=680296) (b:=3)
    (u:=85037) (s:=j+11) (a:=a) (n:=n)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hCsmall (by omega) (by decide) ha heq

#print axioms z_no_special_any_depth
#print axioms x_no_special_any_depth
#print axioms no_special_whole_corridor
#print axioms both_small_from_growth
#print axioms no_special_if_both_small
#print axioms exponential_beats_quintic

#print axioms exact_special_dyadic_depth

#print axioms z_no_special_deep
#print axioms x_no_special_deep
#print axioms z_special_depth_bound
#print axioms x_special_depth_bound
#print axioms special_depth_cutoff
#print axioms no_deep_special

end SheepSpecialDepth

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

#print axioms z_no_special_deep
#print axioms x_no_special_deep
#print axioms z_special_depth_bound
#print axioms x_special_depth_bound
#print axioms special_depth_cutoff
#print axioms no_deep_special

end SheepSpecialDepth

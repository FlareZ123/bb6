import Lean

namespace SheepWeightedResidual

theorem four_pow_mod_nine (n : Nat) : 4^n % 9 = (1+3*n)%9 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rw [ih]
    omega

theorem three_dvd_of_nine_dvd_fourpow (n : Nat) (h : 9 ∣ 4^n-1) : 3 ∣ n := by
  obtain ⟨q,hq⟩ := h
  have hp : 4^n = 9*q+1 := by
    have hpos : 1 ≤ 4^n := Nat.one_le_pow n 4 (by decide)
    omega
  have hpmod : 4^n % 9 = 1 := by rw [hp]; omega
  rw [four_pow_mod_nine] at hpmod
  have hn : (3*n)%9=0 := by omega
  obtain ⟨q2,hq2⟩ := Nat.dvd_of_mod_eq_zero hn
  have hnmod : n%3=0 := by omega
  exact Nat.dvd_of_mod_eq_zero hnmod

theorem four_three_factor (m : Nat) :
    (4^m-1)*(4^(2*m)+4^m+1)+1=4^(3*m) := by
  let x := 4^m
  have hpos : 1 ≤ x := by dsimp [x]; exact Nat.one_le_pow m 4 (by decide)
  have hfactor : (x-1)*(x*x+x+1)+1=x*x*x := by
    rw [Nat.mul_sub_right_distrib]
    simp [Nat.mul_add, Nat.mul_assoc]
    have hprodpos : 1 ≤ x*(x*x) := by
      have hxpos : 0 < x := by omega
      have hxxpos : 0 < x*x := Nat.mul_pos hxpos hxpos
      have hxxxpos : 0 < x*(x*x) := Nat.mul_pos hxpos hxxpos
      omega
    omega
  have h2 : 4^(2*m)=x*x := by
    dsimp [x]
    rw [show 2*m=m+m by omega, Nat.pow_add]
  have h3 : 4^(3*m)=x*x*x := by
    dsimp [x]
    rw [show 3*m=m+2*m by omega, Nat.pow_add, h2]
    ac_rfl
  rw [h2,h3]
  exact hfactor

theorem second_factor_mod_nine (m : Nat) :
    (4^(2*m)+4^m+1)%9=3 := by
  have h1 := four_pow_mod_nine m
  have h2 := four_pow_mod_nine (2*m)
  calc
    (4^(2*m)+4^m+1)%9 = ((4^(2*m)%9 + 4^m%9 + 1)%9) := by simp [Nat.add_mod]
    _ = 3 := by rw [h2,h1]; omega

theorem coprime_three_of_mod3_one (c : Nat) (hc : c%3=1) : Nat.Coprime 3 c := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd 3 c
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left c (by decide)
  have hgdiv3 : g ∣ 3 := by dsimp [g]; exact Nat.gcd_dvd_left 3 c
  have hgdivc : g ∣ c := by dsimp [g]; exact Nat.gcd_dvd_right 3 c
  have hgle : g ≤ 3 := Nat.le_of_dvd (by decide) hgdiv3
  have hmod : 3%g=0 := Nat.mod_eq_zero_of_dvd hgdiv3
  have hgne : g≠3 := by
    intro heq
    rw [heq] at hgdivc
    have hc0 := Nat.mod_eq_zero_of_dvd hgdivc
    omega
  have hne2 : g≠2 := by
    intro heq
    rw [heq] at hmod
    omega
  omega

theorem three_power_dvd_four_pow_sub_one
    (H n : Nat) (hH : 1 ≤ H) (hdiv : 3^H ∣ 4^n-1) : 3^(H-1) ∣ n := by
  induction H generalizing n with
  | zero => omega
  | succ H ih =>
    by_cases hzero : H=0
    · subst H
      simp
    · have hH' : 1 ≤ H := by omega
      have h9 : 9 ∣ 4^n - 1 := by
        have hpow : 3^2 ∣ 3^(H+1) := Nat.pow_dvd_pow 3 (by omega)
        exact Nat.dvd_trans hpow hdiv
      have h3n : 3 ∣ n := three_dvd_of_nine_dvd_fourpow n h9
      obtain ⟨m,hm⟩ := h3n
      let Bfac := 4^(2*m)+4^m+1
      have hBmod : Bfac%9=3 := by dsimp [Bfac]; exact second_factor_mod_nine m
      have hBmod3 : Bfac%3=0 := by omega
      have hBdiv : Bfac=3*(Bfac/3) := by
        have hdecomp := Nat.mod_add_div Bfac 3
        rw [hBmod3] at hdecomp
        omega
      have hcmod : (Bfac/3)%3=1 := by
        have hdecomp9 := Nat.mod_add_div Bfac 9
        rw [hBmod] at hdecomp9
        have hdecomp3 := Nat.mod_add_div Bfac 3
        rw [hBmod3] at hdecomp3
        omega
      let c := Bfac/3
      have hBdiv' : Bfac=3*c := by dsimp [c]; exact hBdiv
      have hcmod' : c%3=1 := by dsimp [c]; exact hcmod
      have hcop3 : Nat.Coprime 3 c := coprime_three_of_mod3_one c hcmod'
      have hcop : Nat.Coprime (3^H) c := Nat.Coprime.pow_left H hcop3
      have hfac : 4^(3*m)-1 = (4^m-1)*Bfac := by
        have hh : (4^m-1)*Bfac+1=4^(3*m) := by
          dsimp [Bfac]
          exact four_three_factor m
        omega
      have hEq : 4^(3*m)-1 = 3*((4^m-1)*c) := by
        calc
          4^(3*m)-1 = (4^m-1)*Bfac := hfac
          _ = (4^m-1)*(3*c) := by rw [hBdiv']
          _ = 3*((4^m-1)*c) := by ac_rfl
      have hdiv' : 3^(H+1) ∣ 4^(3*m)-1 := by simpa [hm] using hdiv
      rw [hEq] at hdiv'
      have hpow3 : 3^(H+1)=3*3^H := by rw [Nat.pow_succ]; ac_rfl
      rw [hpow3] at hdiv'
      have hdivA : 3^H ∣ (4^m-1)*c :=
        Nat.dvd_of_mul_dvd_mul_left (by decide) hdiv'
      have hdivA' : 3^H ∣ 4^m-1 :=
        Nat.Coprime.dvd_of_dvd_mul_right hcop hdivA
      have hIH : 3^(H-1) ∣ m := ih m hH' hdivA'
      have hmul : 3*3^(H-1) ∣ 3*m := Nat.mul_dvd_mul_left 3 hIH
      have hpow : 3^H = 3*3^(H-1) := by
        calc
          3^H = 3^(H-1+1) := by rw [Nat.sub_add_cancel hH']
          _ = 3^(H-1)*3 := by rw [Nat.pow_succ]
          _ = 3*3^(H-1) := by ac_rfl
      have hmul' : 3^H ∣ 3*m := by simpa [hpow] using hmul
      have hexp : H+1-1=H := by omega
      rw [hexp,hm]
      exact hmul'

theorem two_pow_mod_three (B : Nat) :
    2^B%3 = if B%2=0 then 1 else 2 := by
  induction B with
  | zero => decide
  | succ B ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    by_cases h : B%2=0
    · have hsucc : (B+1)%2=1 := by omega
      simp [h, hsucc] at *
      omega
    · have hB : B%2=1 := by omega
      have hsucc : (B+1)%2=0 := by omega
      simp [hB, hsucc] at *
      omega

theorem three_power_dvd_two_pow_sub_one
    (H B : Nat) (hH : 1≤H) (hdiv : 3^H ∣ 2^B-1) :
    2*3^(H-1) ∣ B := by
  have h3 : 3 ∣ 2^B-1 := by
    have hpow : 3^1 ∣ 3^H := Nat.pow_dvd_pow 3 (by omega)
    simpa using Nat.dvd_trans hpow hdiv
  obtain ⟨q,hq⟩ := h3
  have hpowpos : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have hpow : 2^B=3*q+1 := by omega
  have hmod : 2^B%3=1 := by rw [hpow]; omega
  have hBeven : B%2=0 := by
    rw [two_pow_mod_three] at hmod
    by_cases h : B%2=0 <;> simp [h] at hmod <;> omega
  let n := B/2
  have hB : B=2*n := by
    have hdecomp := Nat.mod_add_div B 2
    dsimp [n]
    rw [hBeven] at hdecomp
    omega
  have hpow2 : 2^B=4^n := by
    rw [hB]
    calc
      2^(2*n) = (2^2)^n := by rw [Nat.pow_mul]
      _ = 4^n := by rw [show 2^2=4 by decide]
  have hdiv' : 3^H ∣ 4^n-1 := by rw [← hpow2]; exact hdiv
  have hn : 3^(H-1) ∣ n := three_power_dvd_four_pow_sub_one H n hH hdiv'
  have hmul : 2*3^(H-1) ∣ 2*n := Nat.mul_dvd_mul_left 2 hn
  rw [hB]
  exact hmul

theorem type3_H_ge_9_lower_bound (H B : Nat)
    (hH : 9 ≤ H) (hB : 1 ≤ B) (hdiv : 3^H ∣ 2^B-1) :
    13122 ≤ B := by
  have hmultiple := three_power_dvd_two_pow_sub_one H B (by omega) hdiv
  obtain ⟨k,hk⟩ := hmultiple
  have hkpos : 1 ≤ k := by
    rw [hk] at hB
    have hprod : 0 < (2*3^(H-1))*k := by omega
    have hkpos' : 0 < k := Nat.pos_of_mul_pos_left hprod
    omega
  have hpow : 3^8 ≤ 3^(H-1) :=
    Nat.pow_le_pow_right (by decide : 0 < 3) (by omega)
  have hmul : 2*3^8 ≤ 2*3^(H-1) := Nat.mul_le_mul_left 2 hpow
  have hmul2 : 2*3^(H-1) ≤ 2*3^(H-1)*k := by
    have hh := Nat.mul_le_mul_left (2*3^(H-1)) hkpos
    simpa [Nat.mul_assoc] using hh
  calc
    13122 ≤ 2*3^8 := by decide
    _ ≤ 2*3^(H-1) := hmul
    _ ≤ 2*3^(H-1)*k := hmul2
    _ = B := by rw [hk]


theorem two_pow_mod_five (B : Nat) :
    2^B%5 = if B%4=0 then 1 else if B%4=1 then 2 else if B%4=2 then 4 else 3 := by
  induction B with
  | zero => decide
  | succ B ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    have hcases : B%4=0 ∨ B%4=1 ∨ B%4=2 ∨ B%4=3 := by omega
    rcases hcases with h0|h1|h2|h3
    · have hs : (B+1)%4=1 := by omega
      simp [h0,hs] at *
      omega
    · have hs : (B+1)%4=2 := by omega
      simp [h1,hs] at *
      omega
    · have hs : (B+1)%4=3 := by omega
      simp [h2,hs] at *
      omega
    · have hs : (B+1)%4=0 := by omega
      simp [h3,hs] at *
      omega

theorem four_dvd_of_five_dvd_two_pow_sub_one (B:Nat) (h:5∣2^B-1) : 4∣B := by
  obtain ⟨q,hq⟩ := h
  have hpos :1≤2^B := Nat.one_le_pow B 2 (by decide)
  have hp :2^B=5*q+1 := by omega
  have hmod :2^B%5=1 := by rw [hp]; omega
  rw [two_pow_mod_five] at hmod
  have hB : B%4=0 := by
    have hcases : B%4=0 ∨ B%4=1 ∨ B%4=2 ∨ B%4=3 := by omega
    rcases hcases with h0|h1|h2|h3
    · exact h0
    · simp [h1] at hmod
    · simp [h2] at hmod
    · simp [h3] at hmod
  exact Nat.dvd_of_mod_eq_zero hB

theorem type1_H_ge_3_lower_bound (H B : Nat)
    (hH : 3≤H) (hB : 1≤B)
    (hdiv3 : 3^H∣2^B-1) (hdiv5 : 5∣2^B-1) :
    36≤B := by
  have hdivpow := three_power_dvd_two_pow_sub_one H B (by omega) hdiv3
  have hdiv4 := four_dvd_of_five_dvd_two_pow_sub_one B hdiv5
  obtain ⟨k,hk⟩ := hdiv4
  rw [hk] at hB
  have hkpos : 1≤k := by omega
  rw [hk] at hdivpow
  have hdivk : 3^(H-1)∣2*k := by
    have hh : 2*3^(H-1)∣2*(2*k) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hdivpow
    exact Nat.dvd_of_mul_dvd_mul_left (by decide) hh
  have hcop : Nat.Coprime (3^(H-1)) 2 := Nat.Coprime.pow_left (H-1) (by decide)
  have hdivk' : 3^(H-1)∣k := Nat.Coprime.dvd_of_dvd_mul_left hcop hdivk
  obtain ⟨j,hj⟩ := hdivk'
  have hjpos : 1≤j := by
    rw [hj] at hkpos
    have hprod : 0 < 3^(H-1)*j := by omega
    have hjpos' : 0<j := Nat.pos_of_mul_pos_left hprod
    omega
  have hkge : 3^(H-1)≤k := by
    rw [hj]
    have hh := Nat.mul_le_mul_left (3^(H-1)) hjpos
    simpa using hh
  have hpow : 3^2≤3^(H-1) := Nat.pow_le_pow_right (by decide : 0<3) (by omega)
  calc
    36 ≤ 4*3^2 := by decide
    _ ≤ 4*3^(H-1) := Nat.mul_le_mul_left 4 hpow
    _ ≤ 4*k := Nat.mul_le_mul_left 4 hkge
    _ = B := hk.symm

theorem type1_terminal_H_ge_3_lower_bound (k H B : Nat)
    (hH : 3≤H) (hB : 1≤B)
    (heq : 3^H*(5+135*k)=2^H*(2^B-1)) : 36≤B := by
  have hdivprod3 : 3^H ∣ 2^H*(2^B-1) := by
    refine ⟨5+135*k, ?_⟩
    exact heq.symm
  have hcop3 : Nat.Coprime (3^H) (2^H) :=
    Nat.Coprime.pow H H (by decide)
  have hdiv3 : 3^H ∣ 2^B-1 :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop3 hdivprod3
  have hdivprod5 : 5 ∣ 2^H*(2^B-1) := by
    refine ⟨3^H*(1+27*k), ?_⟩
    have hfac : 5+135*k=5*(1+27*k) := by omega
    calc
      2^H*(2^B-1) = 3^H*(5+135*k) := heq.symm
      _ = 5*(3^H*(1+27*k)) := by rw [hfac]; ac_rfl
  have hcop5 : Nat.Coprime 5 (2^H) := Nat.Coprime.pow_right H (by decide)
  have hdiv5 : 5 ∣ 2^B-1 := Nat.Coprime.dvd_of_dvd_mul_left hcop5 hdivprod5
  exact type1_H_ge_3_lower_bound H B hH hB hdiv3 hdiv5


theorem type3_terminal_H_ge_9_lower_bound (k H B : Nat)
    (hH : 9≤H) (hB : 1≤B)
    (heq : 3^H*(19+1683*k)=2^H*(2^B-1)) : 13122≤B := by
  have hdivprod3 : 3^H ∣ 2^H*(2^B-1) := by
    refine ⟨19+1683*k, ?_⟩
    exact heq.symm
  have hcop3 : Nat.Coprime (3^H) (2^H) :=
    Nat.Coprime.pow H H (by decide)
  have hdiv3 : 3^H ∣ 2^B-1 :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop3 hdivprod3
  exact type3_H_ge_9_lower_bound H B hH hB hdiv3

#print axioms three_power_dvd_four_pow_sub_one
#print axioms three_power_dvd_two_pow_sub_one
#print axioms type3_H_ge_9_lower_bound
#print axioms type1_H_ge_3_lower_bound
#print axioms type1_terminal_H_ge_3_lower_bound
#print axioms type3_terminal_H_ge_9_lower_bound

end SheepWeightedResidual

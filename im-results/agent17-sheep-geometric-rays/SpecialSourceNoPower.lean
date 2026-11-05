import Std

namespace Agent17SheepSpecial
private theorem poly_next (n : Nat) (hn : 4 ≤ n) :
    (n+1)^3+(n+1) ≤ 2*(n^3+n) := by
  have h1 : 4*n ≤ n^2 := by
    simpa only [Nat.pow_two] using Nat.mul_le_mul_right n hn
  have h2 : 4*n^2 ≤ n^3 := by
    simpa [Nat.pow_succ, Nat.pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using Nat.mul_le_mul_right (n*n) hn
  have heq : (n+1)^3+(n+1)=n^3+3*n^2+4*n+2 := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mul_add, Nat.add_mul]
    omega
  rw [heq]
  omega

private theorem poly_pow_shift (n:Nat) :
    (n+14)^3+(n+14) < (2:Nat)^(n+12) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hb := poly_next (n+14) (by omega)
      have hpow : (2:Nat)^(n+1+12) = 2 * 2^(n+12) := by
        rw [show n+1+12=(n+12)+1 by omega, Nat.pow_succ]
        omega
      rw [show n+1+14=(n+14)+1 by omega, hpow]
      omega

theorem poly_lt_pow (a:Nat) (ha:12<=a) :
    (a+2)^3+(a+2) < (2:Nat)^a := by
  have heq : a-12+12=a := by omega
  have ht := poly_pow_shift (a-12)
  have hl : a-12+14=a+2 := by omega
  simpa only [heq, hl] using ht



theorem correction_lt_pow (a h : Nat) (ha : 12 ≤ a)
    (hh : (2:Nat)^h ≤ a+2) :
    3^h*(a+2)+2^h < (2:Nat)^a := by
  have h34 : (3:Nat)^h ≤ 4^h := Nat.pow_le_pow_left (by omega) h
  have h4 : (4:Nat)^h = ((2:Nat)^h)^2 := by
    calc
      (4:Nat)^h = ((2:Nat)^2)^h := by rw [show (4:Nat)=2^2 by decide]
      _ = 2^(2*h) := (Nat.pow_mul 2 2 h).symm
      _ = 2^(h*2) := by rw [Nat.mul_comm]
      _ = (2^h)^2 := Nat.pow_mul 2 h 2
  have h2 : ((2:Nat)^h)^2 ≤ (a+2)^2 := Nat.pow_le_pow_left hh 2
  have h3 : (3:Nat)^h ≤ (a+2)^2 := by omega
  have hprod : (3:Nat)^h*(a+2) ≤ (a+2)^2*(a+2) :=
    Nat.mul_le_mul_right (a+2) h3
  have hpoly := poly_lt_pow a ha
  have hp : (a+2)^2*(a+2)=(a+2)^3 := by exact (Nat.pow_succ (a+2) 2).symm
  omega



theorem no_power_between (a e c b : Nat) (ha : 0 < a)
    (hb : 0 < b) (hblt : b < 2^a) (hc : 1 ≤ c)
    (heq : (2:Nat)^e = c*2^a+b) : False := by
  have hmult : (2:Nat)^a ≤ c*2^a := by
    simpa using Nat.mul_le_mul_right (2^a) hc
  by_cases he : e < a
  · have hlt : (2:Nat)^e < 2^a := Nat.pow_lt_pow_right (by decide) he
    omega
  · have hd : (2:Nat)^a ∣ 2^e := Nat.pow_dvd_pow 2 (by omega)
    have hmod : (2:Nat)^e % 2^a=0 := Nat.mod_eq_zero_of_dvd hd
    rw [heq] at hmod
    have hmod2 : (c*2^a+b)%2^a=b := by
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hblt]
    omega




theorem pow_lower_a (a:Nat) (ha:12≤a)
    (hpoly : (a+2)^3+(a+2) < (2:Nat)^a) :
    a+2 < (2:Nat)^a := by
  have hp : (a+2)^1 ≤ (a+2)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  simp only [Nat.pow_one] at hp
  omega

theorem h_lt_a (a h w : Nat) (ha:12≤a)
    (hsmall : a+2<(2:Nat)^a)
    (heq : 3*2^a+a+2 = 2^h*w) : h<a := by
  by_cases hh : h<a
  · exact hh
  ·
    have hd : (2:Nat)^a ∣2^h := Nat.pow_dvd_pow 2 (by omega)
    have hd2 : (2:Nat)^h ∣ 2^h*w := Nat.dvd_mul_right _ _
    have hd3 : (2:Nat)^a ∣2^h*w := Nat.dvd_trans hd hd2
    have hmod : (2:Nat)^h*w % 2^a=0 := Nat.mod_eq_zero_of_dvd hd3
    rw [←heq] at hmod
    have hmod2 : (3*2^a+a+2)%2^a=a+2 := by
      calc
        (3*2^a+a+2)%2^a = (3*2^a+(a+2))%2^a := by rw [Nat.add_assoc]
        _ = (a+2)%2^a := by simp [Nat.add_mod]
        _ = a+2 := Nat.mod_eq_of_lt hsmall
    omega

theorem v2_small (a h w:Nat) (ha:12≤a)
    (hsmall: a+2<(2:Nat)^a)
    (heq:3*2^a+a+2=2^h*w) : (2:Nat)^h≤a+2 := by
  have hlt := h_lt_a a h w ha hsmall heq
  have hpow : (2:Nat)^h ∣2^a := Nat.pow_dvd_pow 2 (by omega)
  have hprefix : (2:Nat)^h ∣3*2^a :=
    Nat.dvd_trans hpow (Nat.dvd_mul_left (2^a) 3)
  have hall : (2:Nat)^h ∣3*2^a+a+2 := by
    rw [heq]; exact Nat.dvd_mul_right _ _
  have hs : (2:Nat)^h ∣(a+2)+(3*2^a) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  have hd : (2:Nat)^h ∣a+2 := (Nat.dvd_add_left hprefix).mp hs
  exact Nat.le_of_dvd (by omega) hd


theorem special_no_even_power_large (a h w j : Nat) (ha : 12≤a)
    (hfactor : 3*2^a+a+2=2^h*w) : 1+3^h*w≠(2:Nat)^j := by
  intro he
  have hpoly := poly_lt_pow a ha
  have hsmall := pow_lower_a a ha hpoly
  have hv2 := v2_small a h w ha hsmall hfactor
  have hbound := correction_lt_pow a h ha hv2
  have hpow : (2:Nat)^(j+h) = 3^(h+1)*2^a+(3^h*(a+2)+2^h) := by
    calc
      (2:Nat)^(j+h) = 2^j*2^h := by rw [Nat.pow_add]
      _ = (1+3^h*w)*2^h := by rw [he]
      _ = 2^h+(3^h*w)*2^h := by rw [Nat.add_mul, Nat.one_mul]
      _ = 2^h+3^h*(2^h*w) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = 2^h+3^h*(3*2^a+a+2) := by rw [←hfactor]
      _ = 3^(h+1)*2^a+(3^h*(a+2)+2^h) := by
        rw [Nat.pow_succ]
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        omega
  have hbpos : 0 < (3:Nat)^h*(a+2)+2^h := by
    have hp := Nat.pow_pos (by decide : 0 < (2:Nat)) (n:=h)
    omega
  have hcpos : 1 ≤ (3:Nat)^(h+1) := by
    have hp := Nat.pow_pos (by decide : 0 < (3:Nat)) (n:=h+1)
    omega
  exact no_power_between a (j+h) (3^(h+1)) (3^h*(a+2)+2^h) (by omega) hbpos hbound hcpos hpow

#print axioms special_no_even_power_large
private theorem small_outputs_are_not_power (j : Nat) :
    (2:Nat)^j ≠ 10 ∧ (2:Nat)^j ≠ 82 ∧ (2:Nat)^j ≠ 30 ∧
    (2:Nat)^j ≠ 104 ∧ (2:Nat)^j ≠ 676 ∧ (2:Nat)^j ≠ 394 ∧
    (2:Nat)^j ≠ 1168 ∧ (2:Nat)^j ≠ 1548 ∧
    (2:Nat)^j ≠ 6940 ∧ (2:Nat)^j ≠ 6158 := by
  by_cases hj : j < 14
  · have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 := by omega
    rcases hc with c0|c1|c2|c3|c4|c5|c6|c7|c8|c9|c10|c11|c12|c13 <;> subst j <;> decide
  · have hp : (2:Nat)^14 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem special_no_even_power_small (a h w j : Nat) (ha1 : 1 ≤ a) (ha12 : a < 12)
    (hfactor : 3*2^a+a+2=2^h*w) (hwodd : w%2=1) :
    1+3^h*w≠(2:Nat)^j := by
  have hwpos : 1 ≤ w := by omega
  have hs1 : (2:Nat)^h ≤ 2^h*w := by
    have ht := Nat.mul_le_mul_left (2^h) hwpos
    simpa using ht
  have hs2 : 2^h ≤ 3*2^a+a+2 := by omega
  have hbounda : 3*2^a+a+2 < 8192 := by
    have hp : (2:Nat)^a ≤ 2^11 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hboundh : h < 13 := by
    by_cases hh : h < 13
    · exact hh
    · have hp : (2:Nat)^13 ≤ 2^h := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have heval :
      1+3^h*w=10 ∨ 1+3^h*w=82 ∨ 1+3^h*w=30 ∨
      1+3^h*w=104 ∨ 1+3^h*w=676 ∨ 1+3^h*w=394 ∨
      1+3^h*w=1168 ∨ 1+3^h*w=1548 ∨
      1+3^h*w=6940 ∨ 1+3^h*w=6158 := by
    have hc_a : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 := by omega
    have hc_h : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8 ∨ h=9 ∨ h=10 ∨ h=11 ∨ h=12 := by omega
    rcases hc_a with ca1|ca2|ca3|ca4|ca5|ca6|ca7|ca8|ca9|ca10|ca11 <;> subst a <;>
      rcases hc_h with ch0|ch1|ch2|ch3|ch4|ch5|ch6|ch7|ch8|ch9|ch10|ch11|ch12 <;> subst h <;> simp [Nat.pow_succ] at * <;> omega
  rcases small_outputs_are_not_power j with ⟨h10,h82,h30,h104,h676,h394,h1168,h1548,h6940,h6158⟩
  rcases heval with H|H|H|H|H|H|H|H|H|H <;> omega

theorem special_no_even_power (a h w j : Nat) (ha : 1 ≤ a)
    (hfactor : 3*2^a+a+2=2^h*w) (hwodd : w%2=1) :
    1+3^h*w≠(2:Nat)^j := by
  by_cases ht : 12 ≤ a
  · exact special_no_even_power_large a h w j ht hfactor
  · exact special_no_even_power_small a h w j ha (by omega) hfactor hwodd

#print axioms special_no_even_power_small
#print axioms special_no_even_power

end Agent17SheepSpecial

import Lean

namespace BB6.Agent12TwoReset

private theorem poly_step (n d : Nat) (hn : 46 ≤ n) (hd : d ≤ 6) :
    (n+3)^d ≤ 2*(n+2)^d := by
  have hscale : 48*(n+3) ≤ 49*(n+2) := by omega
  have hp := Nat.pow_le_pow_left hscale d
  simp only [Nat.mul_pow] at hp
  have hc : 49^d ≤ 2*48^d := by
    have hcases : d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 := by omega
    rcases hcases with h0|h1|h2|h3|h4|h5|h6 <;> subst d <;> decide
  have hm := Nat.mul_le_mul_right ((n+2)^d) hc
  have hscaled : 48^d*(n+3)^d ≤ 48^d*(2*(n+2)^d) := by
    calc
      _ ≤ 49^d*(n+2)^d := hp
      _ ≤ (2*48^d)*(n+2)^d := hm
      _ = 48^d*(2*(n+2)^d) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.pow_pos (by decide))

/-- Improved final cost inequality, valid from n=46 onwards. -/
theorem sixth_power_budget (n : Nat) (hn : 46 ≤ n) :
    20160*(n+2)^6 < 6*2^n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 46+k := ⟨n-46, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
    have hp := poly_step (46+k) 6 (by omega) (by omega)
    have hm := Nat.mul_le_mul_left 20160 hp
    have he : 6*2^(46+(k+1)) = 2*(6*2^(46+k)) := by
      rw [show 46+(k+1)=(46+k)+1 by omega, Nat.pow_succ]
      omega
    rw [he]
    simp only [show 46+(k+1)+2=(46+k)+3 by omega] at *
    omega

private theorem dominates_linear (n : Nat) (hn : 46 ≤ n) :
    n+4 ≤ 2^n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 46+k := ⟨n-46, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 46+(k+1)=(46+k)+1 by omega, Nat.pow_succ]
    omega

/-- A first-reset subword of polynomial dyadic cost has short (at most
    linear) length. This is the sharpened n=46 threshold ingredient. -/
theorem cube_below_exp (x : Nat) (hx : 48 ≤ x) :
    24*x^3 < 2^x := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 48+k := ⟨x-48, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
    have hp := poly_step (46+k) 3 (by omega) (by omega)
    have hm := Nat.mul_le_mul_left 24 hp
    have he : 2^(48+(k+1))=2*(2^(48+k)) := by
      rw [show 48+(k+1)=(48+k)+1 by omega, Nat.pow_succ]
      omega
    rw [he]
    have hn : (46+k)+2=48+k := by omega
    have hs : (46+k)+3=48+(k+1) := by omega
    rw [hn,hs] at hm
    omega

theorem first_segment_short (n m1 : Nat) (hn : 46 ≤ n)
    (hweight : 2^m1 ≤ 24*(n+2)^3) : m1 ≤ n+2 := by
  have hbound := cube_below_exp (n+2) (by omega)
  have hexp : 2^m1 < 2^(n+2) := by omega
  have hmono := (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hexp
  omega

/-- The second reset's remainder must be below its dyadic modulus. -/
theorem fourth_power_budget (n : Nat) (hn : 46 ≤ n) :
    96*(n+2)^4 < 2^n := by
  have hp : (n+2)^4 ≤ (n+2)^6 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hb := sixth_power_budget n hn
  omega

/-- The final suffix's remainder must be below its dyadic modulus. -/
theorem fifth_power_budget (n : Nat) (hn : 46 ≤ n) :
    576*(n+2)^5 < 2^n := by
  have hp : (n+2)^5 ≤ (n+2)^6 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hb := sixth_power_budget n hn
  omega

/-- Arithmetic contradiction interface for any exact two-positive-reset
    critical P1 wall witness once its source-specific cost bounds are proved. -/
theorem two_reset_budget_contra (n m weight : Nat)
    (hn : 46 ≤ n)
    (hm : m ≤ 11*(n+2))
    (hweight : weight ≤ 576*(n+2)^5)
    (hwall : 7*2^n ≤ n+4+weight*(3*m+2*n+4)) : False := by
  have hlin : 3*m+2*n+4 ≤ 35*(n+2) := by omega
  have hmul := Nat.mul_le_mul hweight hlin
  have hpoly : (576*(n+2)^5)*(35*(n+2)) =
      20160*(n+2)^6 := by
    rw [show (n+2)^6=(n+2)^5*(n+2) by exact Nat.pow_succ (n+2) 5]
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  rw [hpoly] at hmul
  have hdom := dominates_linear n hn
  have hb := sixth_power_budget n hn
  omega

#print axioms sixth_power_budget
#print axioms cube_below_exp
#print axioms first_segment_short
#print axioms fourth_power_budget
#print axioms fifth_power_budget
#print axioms two_reset_budget_contra
end BB6.Agent12TwoReset

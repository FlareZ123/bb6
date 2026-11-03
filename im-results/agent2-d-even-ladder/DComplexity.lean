import Lean.Elab.Tactic.Omega
import DEvenBridge
import DCostLower

namespace BB6.DComplexity
open BB6.DPeriodicEvenBridge
open BB6.DCostLower

private theorem r_le_three_square (r : Nat) : r ≤ 3^(2*r) := by
  induction r with
  | zero => decide
  | succ r ih =>
    have he : 2*(r+1) = (2*r)+2 := by omega
    rw [he, Nat.pow_add]
    have h9 : 3^2=9 := by decide
    rw [h9]
    have hpos : 0 < 3^(2*r) := Nat.pow_pos (by decide)
    omega

/-- Prepared regular F0 input X(k,3r+3), k=9v+7, has finite
    right-tape support 27v+6r+32: only O(3^(2r)) initial cells. -/
theorem even_support (r v U : Nat)
    (hU : U < 512)
    (heq : 512*v+434 = 3^(2*r+1)*U+1) :
    27*v+6*r+32 ≤ 120 * 3^(2*r) := by
  let a := 3^(2*r)
  have hpower : 3^(2*r+1) = 3*a := by
    unfold a
    rw [show 2*r+1=(2*r)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hUup : U ≤ 511 := by omega
  have hmult := Nat.mul_le_mul_left (3*a) hUup
  have hv : v ≤ 3*a := by
    rw [hpower] at heq
    omega
  have hr : r ≤ a := r_le_three_square r
  have ha : 0 < a := Nat.pow_pos (by decide)
  omega

/-- A fully Lean-checked quantitative statement for *all* positive even
    ladder depths. The time is the recursively specified E-ladder primitive
    time; the initial three D machine macros are a separate source contract. -/
theorem even_support_and_cost (r : Nat) (hr : 0 < r) :
    ∃ v U, 0<U ∧ U<512 ∧
      512*v+434 = 3^(2*r+1)*U+1 ∧
      27*v+6*r+32 ≤ 120*3^(2*r) ∧
      64^(2*r) ≤ totalCost (2*r) (U-1) 1 := by
  obtain ⟨v,U,hpos,hlt,hnum,_⟩ := even_bridge_parameters r
  refine ⟨v,U,hpos,hlt,hnum,even_support r v U hlt hnum,?_⟩
  exact totalCost_ge_64pow (2*r) (U-1) 1 (by omega)

/-- The previously known odd-depth bridge uses a fixed multiplier of 256.
    Recurrence avoids any division or parity assumptions. -/
def oddV : Nat → Nat
  | 0 => 4
  | r+1 => 9*oddV r+4

private theorem oddV_power (r : Nat) :
    2*oddV r+1 = 3^(2*r+2) := by
  induction r with
  | zero => decide
  | succ r ih =>
    change 2*(9*oddV r+4)+1 = 3^(2*(r+1)+2)
    have hpow : 3^(2*(r+1)+2) = 9*3^(2*r+2) := by
      rw [show 2*(r+1)+2=(2*r+2)+2 by omega, Nat.pow_add]
      have h9 : 3^2 = 9 := by decide
      rw [h9]
      omega
    rw [hpow]
    omega

/-- Agent35's odd-depth third-endpoint unary identity, and the exact
    packet-size condition, both checked without source-machine assumptions. -/
theorem odd_bridge_parameters (r : Nat) :
    512*oddV r+257 = 3^(2*r+2)*256+1 ∧
    2*(3*r+6)-6 = 3*(2*r+1)+3 := by
  constructor
  · have h := oddV_power r
    omega
  · omega

private theorem three_square_shift (r : Nat) :
    3^(2*r+1) = 3 * 3^(2*r) := by
  rw [show 2*r+1=(2*r)+1 by omega,Nat.pow_succ]
  ac_rfl

private theorem odd_power_shift (r : Nat) :
    3^(2*r+2) = 9 * 3^(2*r) := by
  rw [show 2*r+2=(2*r)+2 by omega,Nat.pow_add]
  have h9 : 3^2=9 := by decide
  rw [h9]
  omega

/-- The odd-depth regular synthetic input fits in 120*3^m cells too. -/
theorem odd_support (r : Nat) :
    27*oddV r+6*r+29 ≤ 120*3^(2*r+1) := by
  let a := 3^(2*r)
  have hpow := oddV_power r
  rw [odd_power_shift] at hpow
  have hthree := three_square_shift r
  have hr : r ≤ a := r_le_three_square r
  have ha : 0 < a := Nat.pow_pos (by decide)
  have hv : oddV r ≤ 5*a := by
    omega
  rw [hthree]
  omega

/-- Uniform size/time complexity for previously known odd-depth entries. -/
theorem odd_support_and_cost (r : Nat) :
    let m := 2*r+1
    let v := oddV r
    512*v+257 = 3^(m+1)*256+1 ∧
    27*v+6*r+29 ≤ 120*3^m ∧
    64^m ≤ totalCost m 255 4 := by
  dsimp
  constructor
  · have h := (odd_bridge_parameters r).1
    simpa [show (2*r+1)+1=2*r+2 by omega] using h
  constructor
  · exact odd_support r
  · exact totalCost_ge_64pow (2*r+1) 255 4 (by omega)

/-- For every positive depth, one of the two fully quantified source
    grammars admits a synthetically prepared *regular* input of size
    at most 120*3^m and an E-time of at least 64^m. The final disjunction
    records the exact third-return source-template matching obligation. -/
theorem all_depth_synthetic (m : Nat) (hm : 0 < m) :
    ∃ k q U p, 0<U ∧ U<512 ∧
      3*k+4+2*q+1 ≤ 120*3^m ∧
      64^m ≤ totalCost m (U-1) p ∧
      ((∃ r v, m=2*r ∧ k=9*v+7 ∧ q=3*r+3 ∧ p=1 ∧
          512*v+434=3^(m+1)*U+1) ∨
        (∃ r v, m=2*r+1 ∧ k=9*v+4 ∧ q=3*r+6 ∧ p=4 ∧
          512*v+257=3^(m+1)*U+1)) := by
  let r := m/2
  have hdiv := Nat.mod_add_div m 2
  rcases Nat.mod_two_eq_zero_or_one m with heven | hodd
  · have hform : m=2*r := by dsimp [r]; omega
    have hr : 0 < r := by omega
    obtain ⟨v,U,hpos,hlt,hnum,hsize,htime⟩ := even_support_and_cost r hr
    refine ⟨9*v+7,3*r+3,U,1,hpos,hlt,?_,?_,Or.inl ?_⟩
    · rw [hform]
      omega
    · rw [hform]
      exact htime
    · refine ⟨r,v,hform,rfl,rfl,rfl,?_⟩
      rw [hform]
      simpa [show (2*r)+1=2*r+1 by omega] using hnum
  · have hform : m=2*r+1 := by dsimp [r]; omega
    have hh := odd_support_and_cost r
    dsimp at hh
    obtain ⟨hnum,hsize,htime⟩ := hh
    refine ⟨9*oddV r+4,3*r+6,256,4,by decide,by decide,?_,?_,Or.inr ?_⟩
    · rw [hform]
      omega
    · rw [hform]
      exact htime
    · refine ⟨r,oddV r,hform,rfl,rfl,rfl,?_⟩
      rw [hform]
      simpa [show (2*r+1)+1=2*r+2 by omega] using hnum

#print axioms even_support
#print axioms even_support_and_cost
#print axioms odd_bridge_parameters
#print axioms odd_support_and_cost
#print axioms all_depth_synthetic
end BB6.DComplexity

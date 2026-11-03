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

#print axioms even_support
#print axioms even_support_and_cost
end BB6.DComplexity

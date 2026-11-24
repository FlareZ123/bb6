import CarryProjection
namespace BB6.Agent28CarryBudget
open BB6.Agent43CarryCert
def budgetOK (n k : Nat) : Bool :=
  decide (requiredMargin n (k+1)+(n+2) ≤ 7*2^(min (n-k) 16))
theorem budget_sound (n k : Nat) (hk : k≤n) (h : budgetOK n k=true) :
    2^k*requiredMargin n (k+1)≤7*2^n-(n+3)+1 := by
  simp only [budgetOK, decide_eq_true_eq] at h
  have hp := Nat.pow_le_pow_right (show 0<2 by decide)
    (show min (n-k) 16≤n-k by omega)
  have hbig := Nat.le_trans h (Nat.mul_le_mul_left 7 hp)
  have hmul := Nat.mul_le_mul_left (2^k) hbig
  rw [Nat.mul_add] at hmul
  have he : 2^k*(7*2^(n-k))=7*2^n := by
    calc
      _ = 7*(2^k*2^(n-k)) := by ac_rfl
      _ = 7*2^n := by rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  rw [he] at hmul
  have h1 : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  have hsmall := Nat.mul_le_mul_right (n+2) h1
  simp only [Nat.one_mul] at hsmall
  omega
#print axioms budget_sound
end BB6.Agent28CarryBudget

import Std
set_option maxHeartbeats 0
namespace CascadeAgent44

private theorem pow_two_nonzero_mod_three (j : Nat) :
    2^j % 3 = 1 ∨ 2^j % 3 = 2 := by
  induction j with
  | zero => left; decide
  | succ j ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h
    · right; omega
    · left; omega

/-- Among 12v, 18v, 27v one lies strictly inside a dyadic
    odd-reset admissible band, for every positive v. -/
theorem three_odd_bands (v : Nat) (hv : 0 < v) :
    (∃ k, 1 ≤ k ∧ 6*2^k+1 ≤ 12*v ∧ 12*v ≤ 8*2^k-1) ∨
    (∃ k, 1 ≤ k ∧ 6*2^k+1 ≤ 18*v ∧ 18*v ≤ 8*2^k-1) ∨
    (∃ k, 1 ≤ k ∧ 6*2^k+1 ≤ 27*v ∧ 27*v ≤ 8*2^k-1) := by
  let x := 3*v
  let j := Nat.log2 x
  let P := 2^j
  have hx : x ≠ 0 := by dsimp [x]; omega
  have hP : P ≤ x := Nat.log2_self_le hx
  have hPu : x < 2*P := by
    have h := Nat.lt_log2_self (n:=x)
    rw [Nat.pow_succ] at h
    simpa [P, Nat.mul_comm] using h
  have hPpos : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hj : 1 ≤ j := by
    apply (Nat.le_log2 hx).mpr
    dsimp [x]
    change 2 ≤ 3*v
    omega
  have hx3 : x = 3*v := rfl
  have hPmod := pow_two_nonzero_mod_three j
  have hboundary : 3*x ≠ 4*P := by
    rcases hPmod with ha | ha <;> omega
  by_cases hlow : 3*x < 4*P
  · right; left
    refine ⟨j,hj,?_,?_⟩
    · dsimp [x] at *
      omega
    · dsimp [x] at *
      omega
  · by_cases hmiddle : 2*x ≤ 3*P
    · right; right
      refine ⟨j+1,by omega,?_,?_⟩
      · rw [Nat.pow_succ]
        dsimp [x] at *
        omega
      · rw [Nat.pow_succ]
        dsimp [x] at *
        omega
    · left
      refine ⟨j,hj,?_,?_⟩
      · dsimp [x] at *
        omega
      · dsimp [x] at *
        omega

#print axioms three_odd_bands
end CascadeAgent44

import BParityCodingSource

namespace BB6.BParityRuns

/-- The complete self-indexing return map in shifted generalized 3x+7 coordinates. -/
def collatzA : Nat → Nat
  | 0 => 3
  | n+1 =>
      let x := iterC (collatzA n) 8
      x + 1 - 3*(x%2)

/-- The diagonal return indices are exactly the original Machine B indices. -/
theorem collatzA_eq_scalarA (n : Nat) : collatzA n = OneDim.scalarA n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [collatzA, OneDim.scalarA, ih]
      have h0 : iterC (OneDim.scalarA n) 8 = OneDim.iterG (OneDim.scalarA n) 0 + 8 := by
        have hs := shift_iter (OneDim.scalarA n) 0
        rw [source_iterG] at hs
        simpa only [Nat.zero_add] using hs.symm
      rw [h0]
      omega

/-- Every sampled scalar bit agrees with the dynamically self-indexed 3x+7 bit. -/
theorem collatz_sample_bit (n : Nat) :
    (OneDim.iterG (OneDim.scalarA n) 0)%2 =
      (iterC (collatzA n) 8)%2 := by
  rw [collatzA_eq_scalarA]
  have h : iterC (OneDim.scalarA n) 8 = OneDim.iterG (OneDim.scalarA n) 0 + 8 := by
    have hs := shift_iter (OneDim.scalarA n) 0
    rw [source_iterG] at hs
    simpa only [Nat.zero_add] using hs.symm
  rw [h]
  omega

/-- Every source-machine scalar reset index (and hence Collatz diagonal) is odd. -/
theorem scalarA_odd (n : Nat) : OneDim.scalarA n%2=1 := by
  cases n with
  | zero => decide
  | succ n =>
      simp only [OneDim.scalarA]
      have hmod : (OneDim.iterG (OneDim.scalarA n) 0)%2=0 ∨
          (OneDim.iterG (OneDim.scalarA n) 0)%2=1 := by omega
      rcases hmod with he | ho
      · rw [he]; omega
      · rw [ho]; omega

theorem collatzA_odd (n : Nat) : collatzA n%2=1 := by
  rw [collatzA_eq_scalarA]
  exact scalarA_odd n

#print axioms collatzA_eq_scalarA
#print axioms collatz_sample_bit
#print axioms collatzA_odd
end BB6.BParityRuns

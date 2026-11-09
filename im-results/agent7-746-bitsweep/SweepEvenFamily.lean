import SweepEvenOrbit

namespace CascadeFastReturn
open CascadeBitSweep

/-- A simple exponential dominates the block-length margin. -/
private theorem block_margin (m : Nat) : 4*m+26 ≤ 4*2^(m+10) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have he : 2^(m+1+10) = 2*2^(m+10) := by
      rw [show m+1+10 = (m+10)+1 by omega, Nat.pow_succ]
      omega
    rw [he]
    omega

/-- An explicitly constructed exact source reset block for every length m. -/
theorem arbitrarily_long_even_block (m : Nat) :
    runBit (atHeight (2*m+10) m (4*m+26)) m =
      some (atHeight (2*m+10) 0 (4*m+26)) := by
  let k := 2*m+10
  let d := 4*m+26
  have hd : 2*k+6 ≤ d := by dsimp [k,d]; omega
  have hpow : 2^k = 2^m*2^(m+10) := by
    dsimp [k]
    rw [show 2*m+10=m+(m+10) by omega, Nat.pow_add]
  have hscale : 2^m*d ≤ 4*2^k := by
    calc
      2^m*d ≤ 2^m*(4*2^(m+10)) := Nat.mul_le_mul_left _ (by simpa [d] using block_margin m)
      _ = 4*2^k := by rw [hpow]; simp [Nat.mul_left_comm]
  have hlow : 4*2^k ≤ atHeight k m d := by
    dsimp [atHeight]
    omega
  exact runBit_even_block k m d hd hlow

#print axioms arbitrarily_long_even_block
end CascadeFastReturn

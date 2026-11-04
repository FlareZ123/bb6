import FirstInverseComplete

namespace CascadeResetInverse

private theorem three_dominates_two (t : Nat) : 3*2^t ≤ 3^(t+1) := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    omega

/-- The direct first-reset graph has the strict natural-number ranking h<u.
    In particular every reverse ancestral chain is finite. -/
theorem reset_parent_strict (h u : Nat) (hp : ResetParent h u) : h < u := by
  rcases hp with ⟨k,⟨hl,hu⟩,heq⟩ | ⟨k,t,d,hd,⟨hl,hu⟩,hout,hq⟩
  · have hp0 : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    have hb : u+3 ≤ 8*2^k := by omega
    omega
  · have hbase : 3*2^t ≤ 3^(t+1) := three_dominates_two t
    have hmul := Nat.mul_le_mul_right d hbase
    have hc : 3*(2^t*d) ≤ 3^(t+1)*d := by
      calc
        3*(2^t*d) = (3*2^t)*d := by simp [Nat.mul_assoc]
        _ ≤ 3^(t+1)*d := hmul
    have hpow : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    have hq : 7 ≤ 2^t*d := by omega
    have hqu : 2^t*d ≤ u := by omega
    omega

#print axioms reset_parent_strict
end CascadeResetInverse

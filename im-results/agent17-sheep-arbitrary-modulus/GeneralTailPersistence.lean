import Std
import Lean.Elab.Tactic.Omega

namespace BB6Sheep17GeneralTail
/-- Once the generic inverse residue gap holds at one valuation,
and the power-of-two modulus exceeds the linear increment reserve,
it continues to hold when the valuation increases. -/
theorem tail_persists (c d k m : Nat)
    (hc : c < k)
    (hm : c * (c + k) + k < m)
    (hd : 2 * d * (c + 1) + 1 <= m) :
    c < k + 2 * d ∧
    c * (c + (k + 2 * d)) + (k + 2 * d) < 2 * m - 1 ∧
    2 * d * (c + 1) + 1 <= 2 * m - 1 := by
  have hmul : c * (c + (k + 2*d)) + (k + 2*d) =
      (c*(c+k)+k) + (2*d*(c+1)) := by
    simp only [Nat.mul_add, Nat.mul_one]
    ac_rfl
  constructor
  · omega
  constructor
  · rw [hmul]
    omega
  · omega

#print axioms tail_persists
end BB6Sheep17GeneralTail

import Agent10GrowthSource

namespace BB6.Agent10B

/-- Base-two tetration sequence, tower 0 = 2, tower (n+1) = 2^(tower n). -/
def tower : Nat → Nat
  | 0 => 2
  | n+1 => 2^(tower n)

theorem tower_pos (n : Nat) : 0 < tower n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [tower]
    exact Nat.pow_pos (by decide)

/-- Every actual syntactic reset index dominates a full base-two power tower. -/
theorem reset_dominates_tower (n : Nat) :
    2*tower n ≤ BB6.OneDim.scalarA (n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hs := scalarA_exponential_step (n+1)
    have hd : tower n ≤ BB6.OneDim.scalarA (n+1)/2 := by omega
    have hp : 2^(tower n) ≤ 2^(BB6.OneDim.scalarA (n+1)/2) :=
      Nat.pow_le_pow_right (by decide : 0<2) hd
    have hm := Nat.mul_le_mul_left 10 hp
    have hpos : 0 < 2^(tower n) := Nat.pow_pos (by decide)
    change 2*(2^(tower n)) ≤ BB6.OneDim.scalarA (n+1+1)
    omega

#print axioms reset_dominates_tower
end BB6.Agent10B

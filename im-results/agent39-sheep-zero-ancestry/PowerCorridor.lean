import ZeroAncestry
import ThreeAdicOrder

namespace BB6.Agent39Sheep

open BB6.Agent39Three (power_cong_iff_exponent)

/-- A power 2^j with j≥3 admits a generic zero-valuation inverse corridor
    of length k+1 exactly when its exponent is divisible by 2*3^k. -/
theorem power_corridor_iff (k j : Nat) (hj : 3 ≤ j) :
    (∃ x, Chain0 (k+1) x (2^j)) ↔ 2*3^k ∣ j := by
  have hpos : 5 ≤ 2^j := by
    have hh : (2:Nat)^3 ≤ 2^j :=
      Nat.pow_le_pow_right (by decide) hj
    omega
  rw [chain_target_iff_divisible (k+1) (2^j) hpos]
  have he : (3^(k+1) ∣ 2^j-1) ↔
      (∃ m, 2^j = 1+3^(k+1)*m) := by
    constructor
    · rintro ⟨m,hm⟩
      refine ⟨m, ?_⟩
      omega
    · rintro ⟨m,hm⟩
      refine ⟨m, ?_⟩
      omega
  exact he.trans (power_cong_iff_exponent k j)

/-- Whenever the sharp exponent divisibility condition holds, precisely one
    zero-valuation ancestor exists at the requested depth. -/
theorem power_corridor_unique (k j : Nat) (hj : 3≤j)
    (hd : 2*3^k ∣ j) :
    ∃ x, Chain0 (k+1) x (2^j) ∧
      ∀ x' : Nat, Chain0 (k+1) x' (2^j) → x'=x := by
  obtain ⟨x,hc⟩ := (power_corridor_iff k j hj).mpr hd
  refine ⟨x,hc,?_⟩
  intro x' hc'
  exact chain_unique_source hc' hc

#print axioms BB6.Agent39Sheep.power_corridor_iff
#print axioms BB6.Agent39Sheep.power_corridor_unique
end BB6.Agent39Sheep

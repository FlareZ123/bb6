import PowerCorridor

namespace BB6.Agent39Sheep
open BB6.Agent39Three (W pow_one_mod)

/-- Explicit exponent family in each of 100 residue classes divisible by 54
    modulo 5400. -/
def exponent54 (s k : Nat) : Nat := 54*s*3^(40*k)

private theorem forty_power :
    3^40 = 1+100*121576654590569288 := by decide

theorem exponent54_class (s k : Nat) :
    exponent54 s k %5400 = (54*s)%5400 := by
  have hp : 3^(40*k) = 1+100*W 100 121576654590569288 k := by
    rw [Nat.pow_mul, forty_power]
    exact pow_one_mod 100 121576654590569288 k
  unfold exponent54
  rw [hp]
  have he : 54*s*(1+100*W 100 121576654590569288 k) =
      54*s+5400*(s*W 100 121576654590569288 k) := by
    simp only [Nat.mul_add, Nat.mul_one]
    have h5400 : 5400=54*100 := by decide
    rw [h5400]
    ac_rfl
  rw [he]
  omega

theorem exponent54_divisible (s k : Nat) :
    2*3^k ∣ exponent54 s k := by
  refine ⟨27*s*3^(39*k), ?_⟩
  unfold exponent54
  have he : 40*k=k+39*k := by omega
  rw [he,Nat.pow_add]
  have hf : 54=2*27 := by decide
  rw [hf]
  ac_rfl

theorem exponent54_large (s k : Nat) (hs:1≤s) :
    3≤exponent54 s k := by
  unfold exponent54
  have hp : 0<3^(40*k) := Nat.pow_pos (by decide)
  have hmul : 54*s ≤ 54*s*3^(40*k) :=
    Nat.le_mul_of_pos_right _ hp
  omega

/-- Every residue r≡0(mod54) modulo 5400 has arbitrarily deep genuine
    zero-valuation predecessor corridors. This obstructs uniform fixed-depth
    inverse-tree certificates based only on exhausted predecessors. -/
theorem all_hundred_residue_classes_have_deep_ancestors
    (s k : Nat) (hs:1≤s) :
    ∃ j x, j%5400 = (54*s)%5400 ∧
      Chain0 (k+1) x (2^j) := by
  let j := exponent54 s k
  have hj : 3≤j := exponent54_large s k hs
  obtain ⟨x,hx⟩ := (power_corridor_iff k j hj).mpr
    (exponent54_divisible s k)
  exact ⟨j,x,exponent54_class s k,hx⟩

#print axioms all_hundred_residue_classes_have_deep_ancestors
end BB6.Agent39Sheep

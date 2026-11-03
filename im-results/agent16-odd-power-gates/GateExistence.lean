module
public import OddPredecessor
@[expose] public section
namespace BB6.Agent16OddPower

/-- The exact odd multiplier of the unique even source at eligible powers. -/
def gateOdd : Nat → Nat
  | 0 => 3
  | k+1 => 16 * gateOdd k + 3

theorem gateOdd_equation (k : Nat) : 5 * gateOdd k + 1 = 2^(4*k+4) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have he : 4*(k+1)+4=(4*k+4)+4 := by omega
      rw [he, Nat.pow_add]
      have h16 : 2^4=16 := by decide
      rw [h16]
      simp only [gateOdd]
      omega

theorem gateOdd_odd (k : Nat) : gateOdd k % 2=1 := by
  induction k with
  | zero => decide
  | succ k ih => simp only [gateOdd]; omega

private theorem gateOdd_min (k : Nat) : 3 ≤ gateOdd k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [gateOdd]; omega

theorem gateOdd_large (k : Nat) (hk : 1≤k) : 5≤gateOdd k := by
  cases k with
  | zero => omega
  | succ k =>
      have hp : 3≤gateOdd k := gateOdd_min k
      simp only [gateOdd]
      omega

theorem gate_eligible_source (k : Nat) (hk : 1≤k) :
    SectionStep (2*gateOdd k) (2^(4*k+3)) := by
  apply section_power_iff.mpr
  refine ⟨gateOdd k, gateOdd_large k hk, gateOdd_odd k, rfl, ?_⟩
  have h : 4*k+3+1=4*k+4 := by omega
  rw [h]
  exact gateOdd_equation k

/-- COMPLETE, uniform if-and-only-if: direct even-section powers exist
    at exactly the exponents j=7,11,15,... . -/
theorem even_section_power_possible (j : Nat) :
  (∃ x, SectionStep x (2^j)) ↔ 7≤j ∧ j%4=3 := by
  constructor
  · rintro ⟨x,hx⟩
    have hr : j%4=3 := all_power_section_exponent hx
    obtain ⟨u,hu,ho,hx2,hpow⟩ := all_power_section_parent hx
    have hj : 4≤j := by
      by_cases hsmall : j≤3
      · have hp : 2^(j+1)≤2^4 := Nat.pow_le_pow_right (by decide) (by omega)
        have h16 : 2^4=16 := by decide
        rw [h16] at hp
        omega
      · omega
    exact ⟨by omega, hr⟩
  · rintro ⟨hj,hr⟩
    let k:=j/4
    have hk : 1≤k := by dsimp [k]; omega
    have he : j=4*k+3 := by dsimp [k]; omega
    rw [he]
    exact ⟨2*gateOdd k, gate_eligible_source k hk⟩

/-- At most one even-section source can feed any power, at every exponent. -/
theorem even_section_power_unique {x y j : Nat}
    (hx : SectionStep x (2^j)) (hy : SectionStep y (2^j)) : x=y := by
  obtain ⟨u,hu,ho,hxu,heu⟩ := all_power_section_parent hx
  obtain ⟨v,hv,hvo,hyv,hev⟩ := all_power_section_parent hy
  omega

#print axioms gate_eligible_source
#print axioms even_section_power_possible
#print axioms even_section_power_unique
end BB6.Agent16OddPower

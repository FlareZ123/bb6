module
public import OddEvenGate
public import SecondExceptional
@[expose] public section
namespace BB6.Agent16OddEvenGate

/-- All genuine even returns to an odd-power gateway have h=0. -/
theorem second_gate_even_direct {s k : Nat}
  (he : SheepEven.EvenEdge s (2*BB6.Agent16OddPower.gateOdd k))
  (hs : s%2=0) :
  BB6.Agent16OddPower.SectionStep s (2*BB6.Agent16OddPower.gateOdd k) := by
  obtain ⟨z,h,u,hstep,hz5,hu,hz,hy⟩ := he
  have hp : (2*BB6.Agent16OddPower.gateOdd k)%3=0 := by
    rw [Nat.mul_mod,BB6.Agent16OddPower.gateOdd_div3]
  have hh : h=0 := by
    by_cases hh : h=0
    · exact hh
    · exfalso
      obtain ⟨v,hv⟩ : ∃v, h=v+1 := ⟨h-1,by omega⟩
      rw [hv,Nat.pow_succ] at hy
      have hzero : ((3^v*3)*u)%3=0 := by
        have hm : (3^v*3)*u = 3*(3^v*u) := by ac_rfl
        rw [hm]
        simp
      rw [hy] at hp
      omega
  subst h
  have hz' : z=2*BB6.Agent16OddPower.gateOdd k := by
    simp only [Nat.pow_zero, Nat.one_mul] at hz hy
    omega
  rw [←hz']
  exact BB6.Agent16OddPowerSource.even_section_to_local
    (BB6.Agent16.SheepEvenSource.even_to_section hstep) hs

/-- The source immediately before any actual even-return to the unique
    odd-power source has small 2-adic valuation. -/
theorem second_even_parent_valuation_small {s k : Nat}
    (he : SheepEven.EvenEdge s (2*BB6.Agent16OddPower.gateOdd k))
    (hs : s%2=0) :
    ∃ a v, 1≤a ∧ a≤5 ∧ 5≤v ∧ v%2=1 ∧ s=2^a*v ∧
      2^a*v+a+(v-1)/2=2*BB6.Agent16OddPower.gateOdd k := by
  exact BB6.Agent16OddPower.second_parent_valuation_small (second_gate_even_direct he hs)

#print axioms second_gate_even_direct
#print axioms second_even_parent_valuation_small
end BB6.Agent16OddEvenGate

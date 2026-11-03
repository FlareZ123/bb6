module
public import EvenSourceBridge
public import OddPowerSource
@[expose] public section
namespace BB6.Agent16OddEvenGate

/-- Genuine E edges at odd-exponent powers, with genuine even sources. -/
theorem even_odd_power_possible (j : Nat) (hj : j%2=1) :
  (∃ x, x%2=0 ∧ SheepEven.EvenEdge x (2^j)) ↔
    7≤j ∧ j%4=3 := by
  constructor
  · rintro ⟨x,hx,he⟩
    obtain ⟨z,h,u,hs,hz5,ho,hz,hy⟩ := he
    have hs' : BB6.Agent16OddPower.SectionStep x z :=
      BB6.Agent16OddPowerSource.even_section_to_local
        (BB6.Agent16.SheepEvenSource.even_to_section hs) hx
    have hlocal : BB6.Agent16OddPower.FirstEvenEdge x (2^j) :=
      ⟨z,h,u,hs',ho,hz,hy⟩
    obtain ⟨v,hv,hvo,hxv,heq⟩ :=
      BB6.Agent16OddPower.odd_power_parent_shape hj hlocal
    have hdirect : BB6.Agent16OddPower.SectionStep x (2^j) :=
      (BB6.Agent16OddPower.section_power_iff).mpr ⟨v,hv,hvo,hxv,heq⟩
    exact (BB6.Agent16OddPower.even_section_power_possible j).mp ⟨x,hdirect⟩
  · intro hr
    obtain ⟨x,hx,hs⟩ := (BB6.Agent16OddPowerSource.source_even_power_possible j).mpr hr
    have hstep : SheepEven.Step x (2^j) :=
      BB6.Agent16.SheepEvenSource.section_to_even hs
    have htwopos : 5≤2^j := by
      have hp : 2^3≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have heven : (2^j)%2=0 := by
      have hp : 0<j := by omega
      have hrepr : j=(j-1)+1 := by omega
      rw [hrepr, Nat.pow_succ]
      omega
    let u:=2^j-1
    have huodd : u%2=1 := by dsimp [u]; omega
    have hunit : 1+u=2^j := by dsimp [u]; omega
    refine ⟨x,hx, ⟨2^j,0,u,hstep,htwopos,huodd,?_,?_⟩⟩
    · simp only [Nat.pow_zero, Nat.one_mul]
      exact hunit.symm
    · simp only [Nat.pow_zero, Nat.one_mul]
      exact hunit.symm

#print axioms even_odd_power_possible
end BB6.Agent16OddEvenGate

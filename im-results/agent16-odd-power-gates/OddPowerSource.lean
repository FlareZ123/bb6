module

public import SheepSourceBridge
public import GateExistence

@[expose] public section

namespace BB6.Agent16OddPowerSource

open BB6.Agent16OddPower

/-- The actual machine-certified Sheep section step, on even sources,
is exactly the source-independent positive-valuation local relation. -/
theorem even_section_to_local {x y : Nat}
  (h : SheepBridge.SectionNext x y) (he : x % 2 = 0) :
    SectionStep x y := by
  cases h with
  | triple a =>
      have ha : 1 ≤ a := by
        cases a with
        | zero => simp at he
        | succ k => omega
      exact SectionStep.special a ha
  | general a u hu hodd =>
      have ha : 1 ≤ a := by
        cases a with
        | zero => simp at he; omega
        | succ k => omega
      exact SectionStep.generic a u ha hu hodd

/-- All genuine even-source return edges into a power of 2 have j % 4 = 3. -/
theorem source_even_section_power_gate {x j : Nat}
  (h : SheepBridge.SectionNext x (2^j)) (he : x % 2 = 0) :
    j % 4 = 3 :=
  all_power_section_exponent (even_section_to_local h he)

/-- Complete source-level inverse equation, without finite-depth assumptions. -/
theorem source_even_section_power_iff {x j : Nat} (he : x % 2 = 0) :
    SheepBridge.SectionNext x (2^j) ↔
    ∃ u, 5 ≤ u ∧ u % 2 = 1 ∧ x = 2*u ∧ 5*u+1 = 2^(j+1) := by
  constructor
  · intro h
    exact (section_power_iff).mp (even_section_to_local h he)
  · intro h
    obtain ⟨u,hu,hodd,hx,hpower⟩ := h
    have hz : (2^1*u+1+(u-1)/2) = 2^j := by
      have hd : 2*((u-1)/2)=u-1 := by omega
      have hp : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]; omega
      simp only [show 2^1=2 by decide]
      omega
    rw [hx, ←hz]
    exact SheepBridge.SectionNext.general 1 u hu hodd

theorem local_to_source {x y : Nat} (h : SectionStep x y) :
    SheepBridge.SectionNext x y := by
  cases h with
  | special a ha => exact SheepBridge.SectionNext.triple a
  | generic a u ha hu hodd => exact SheepBridge.SectionNext.general a u hu hodd

/-- Complete source-authentic classification of possible one-return even gateways. -/
theorem source_even_power_possible (j : Nat) :
    (∃ x, x%2=0 ∧ SheepBridge.SectionNext x (2^j)) ↔
      7≤j ∧ j%4=3 := by
  constructor
  · rintro ⟨x,he,hs⟩
    exact (even_section_power_possible j).mp ⟨x,even_section_to_local hs he⟩
  · intro hr
    obtain ⟨x,hx⟩ := (even_section_power_possible j).mpr hr
    obtain ⟨u,hu,hodd,heq,hpower⟩ := all_power_section_parent hx
    refine ⟨x,?_,local_to_source hx⟩
    rw [heq]
    omega

/-- The authentic section graph has at most one even parent of each power. -/
theorem source_even_power_unique {x y j : Nat}
  (hx : SheepBridge.SectionNext x (2^j)) (hy : SheepBridge.SectionNext y (2^j))
  (hex : x%2=0) (hey : y%2=0) : x=y :=
    even_section_power_unique (even_section_to_local hx hex) (even_section_to_local hy hey)

#print axioms source_even_power_possible
#print axioms source_even_power_unique
#print axioms even_section_to_local
#print axioms source_even_section_power_gate
#print axioms source_even_section_power_iff

end BB6.Agent16OddPowerSource

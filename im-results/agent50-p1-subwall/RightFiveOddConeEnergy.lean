import RightFiveNearDouble

namespace BB6.Agent50OddConeEnergy
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent50Energy BB6.Agent50EnergyParam

/-- Source-original all-endpoint energy gap without choosing a counted witness.
Uniform over every source OddCone inverse word and every right counter. -/
theorem source_odd_cone_energy_gap_param
    (n M b d m : Nat) (hn : 14≤n) (hM : M≤n)
    (hNum : 64*(n+2)*(n+2)*2^M≤2^n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m)
    (hm : m≤M) :
    (12*2^n < b+4*m+4*n+20 ∨
      (b+4*m+4*n+20)+threshold n M m ≤12*2^n) := by
  obtain ⟨z,hcount⟩ := odd_cone_has_count _ _ _ _ _ h
  exact source_energy_budget_gap_param n M b d m z hn hM hNum hcount hm

/-- Source-original OddCone itself admits a faithful positive reset count,
and any right-five history requires at least three positive depth resets,
without a cost or inverse-word-length restriction. -/
theorem source_odd_cone_right_five_three_resets
    (n b m : Nat) (hn : 14≤n)
    (h : OddCone (14*2^n-2*n-16) 3 b 5 m) :
    ∃ z, CountCone (14*2^n-2*n-16) 3 b 5 m z ∧ 3≤z := by
  obtain ⟨z,hcount⟩ := odd_cone_has_count _ _ _ _ _ h
  exact ⟨z,hcount,BB6.Agent50RightFiveThree.source_right_five_needs_three_resets
    n b m z hn hcount⟩

#print axioms BB6.Agent50OddConeEnergy.source_odd_cone_energy_gap_param
#print axioms BB6.Agent50OddConeEnergy.source_odd_cone_right_five_three_resets

end BB6.Agent50OddConeEnergy

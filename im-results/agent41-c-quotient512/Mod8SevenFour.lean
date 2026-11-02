import CSourceBridge8
set_option maxRecDepth 16384

namespace CCert

-- The entire two-parameter congruence cylinder avoids the
-- fully kernel-certified abstract blank-entry orbit.
theorem seven_four_abstract_exclusion (u v : Nat) :
    seen (q (8*u+7)) (q (8*v+4)) (q 0) = false := by
  rcases u with _ | u
  · rcases v with _ | v
    · decide
    · have hk : q (8*(v+1)+4) = q 12 :=
        q_congr_big _ _ (by omega) (by omega) (by omega)
      rw [hk]
      decide
  · have ha : q (8*(u+1)+7) = q 15 :=
      q_congr_big _ _ (by omega) (by omega) (by omega)
    rw [ha]
    rcases v with _ | v
    · decide
    · have hk : q (8*(v+1)+4) = q 12 :=
        q_congr_big _ _ (by omega) (by omega) (by omega)
      rw [hk]
      decide

-- This Reach is the exact original published Machine C accelerator,
-- rather than merely an independently copied finite simulation.
theorem published_no_seven_four (u v : Nat) :
    ¬ BB6CLine.Reach (8*u+7, 8*v+4, 0) := by
  intro h
  have hs := reachable_seen (source_reachable_embeds h)
  have hfalse := seven_four_abstract_exclusion u v
  rw [hfalse] at hs
  cases hs

-- Among the source-certified two-parameter immediate-stopping section
-- equations, two entire j,m residue cylinders lie in the forbidden family.
-- This is a reachability implication, not a claim that Machine C never halts.
theorem published_no_odd_halting_parameter_pair
    (j m k : Nat)
    (hj : (j % 8 = 2 ∧ m % 8 = 7) ∨
          (j % 8 = 6 ∧ m % 8 = 3))
    (hk : k + j + 3*m + 5 = 2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hm : 0 < m := by
    rcases hj with h | h <;> omega
  have hpow : 8 ∣ 2^(2*m+2) := by
    obtain ⟨r,hr⟩ : ∃ r, 2*m+2 = 3+r := ⟨2*m-1, by omega⟩
    rw [hr, Nat.pow_add]
    change 8 ∣ 8*2^r
    exact ⟨2^r,rfl⟩
  have hproduct : 8 ∣ 2^(2*m+2)*(j+3) := by
    rcases hpow with ⟨z,hz⟩
    refine ⟨z*(j+3), ?_⟩
    rw [hz]
    simp only [Nat.mul_assoc]
  have hmod : (k+j+3*m+5)%8=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hproduct
  have hresj : j % 4 = 2 := by
    rcases hj with h | h <;> omega
  have hk4 : k % 8 = 4 := by
    rcases hj with h | h <;> omega
  have hA : 2*j+3=8*(j/4)+7 := by omega
  have hK : k=8*(k/8)+4 := by omega
  rw [hA,hK]
  exact published_no_seven_four (j/4) (k/8)

#print axioms seven_four_abstract_exclusion
#print axioms published_no_seven_four
#print axioms published_no_odd_halting_parameter_pair
end CCert

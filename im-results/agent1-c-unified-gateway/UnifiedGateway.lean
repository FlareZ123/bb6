import BlankParam
import UnifiedArithmetic

namespace BB6.Agent1Unified
open BB6.Agent46

/-- Original Machine C two-counter first-return map: the complete nonzero
    stopping locus is one base-four Diophantine equation. -/
theorem source_section_halts_iff_one_equation (a k : Nat) :
    secNext (a,k) = none ↔
      ((a=0 ∧ k=0) ∨
       (0<a ∧ a%2=1 ∧ ∃ m : Nat,
         a+2*k+6*m+7 = 4^(m+1)*(a+3))) := by
  exact (BB6.Agent15.section_halts_iff_parametric a k).trans
    (or_congr Iff.rfl (two_families_iff_one_four_power a k))

/-- Genuine blank-origin Machine C: exact machine halting iff the actual
    source-connected section reaches the single unified dyadic gate. -/
theorem source_blank_halts_iff_one_equation :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k, BB6.Agent8Section.run secNext time (some (5,1)) = some (a,k) ∧
        (0<a ∧ a%2=1 ∧ ∃ m : Nat,
          a+2*k+6*m+7 = 4^(m+1)*(a+3)) := by
  rw [BB6.Agent15.blank_halts_iff_two_parametric_families]
  constructor
  · rintro ⟨time,a,k,hreach,halt⟩
    exact ⟨time,a,k,hreach,(two_families_iff_one_four_power a k).mp halt⟩
  · rintro ⟨time,a,k,hreach,halt⟩
    exact ⟨time,a,k,hreach,(two_families_iff_one_four_power a k).mpr halt⟩

#print axioms source_section_halts_iff_one_equation
#print axioms source_blank_halts_iff_one_equation
end BB6.Agent1Unified

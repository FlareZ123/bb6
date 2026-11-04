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

/-- The odd-right/source-image obstruction excludes one joint residue class
    of the unified parameterized stopping locus, at every blank orbit time. -/
theorem bad_level_unreachable (time u k m : Nat)
    (hreach : BB6.Agent8Section.run secNext time (some (5,1)) =
       some (2*u+1,k))
    (heq : (2*u+1)+2*k+6*m+7 = 4^(m+1)*((2*u+1)+3))
    (hmod : (u+m)%4=1) : False := by
  obtain ⟨hk,hs⟩ := bad_level_residues u k m hmod heq
  have hstart := BB6Agent38.blank_section_mod4 time (2*u+1) k hreach hk hs
  have hhalt : secNext (2*u+1,k)=none :=
    (source_section_halts_iff_one_equation (2*u+1) k).mpr
      (Or.inr ⟨by omega,by omega,m,heq⟩)
  have hhaltStart : secNext (5,1)=none := by
    simpa [hstart] using hhalt
  have hnon : secNext (5,1) ≠ none := by decide
  exact hnon hhaltStart

/-- All-time genuine blank-origin stop iff one *filtered* unified gate.
    The excluded congruence addresses both earlier halting branches. -/
theorem source_blank_halts_iff_filtered :
    BB6.CReachBridge.RunHalts ↔
      ∃ time u k m, BB6.Agent8Section.run secNext time (some (5,1)) =
        some (2*u+1,k) ∧
        (2*u+1)+2*k+6*m+7 = 4^(m+1)*((2*u+1)+3) ∧
        (u+m)%4 ≠ 1 := by
  rw [source_blank_halts_iff_one_equation]
  constructor
  · rintro ⟨time,a,k,hreach,ha,hodd,m,hm⟩
    let u := (a-1)/2
    have hae : a=2*u+1 := by dsimp [u]; omega
    rw [hae] at hreach hm
    refine ⟨time,u,k,m,hreach,hm,?_⟩
    intro hmod
    exact bad_level_unreachable time u k m hreach hm hmod
  · rintro ⟨time,u,k,m,hreach,hm,_⟩
    exact ⟨time,2*u+1,k,hreach,by omega,by omega,m,hm⟩

#print axioms bad_level_unreachable
#print axioms source_blank_halts_iff_filtered
#print axioms source_section_halts_iff_one_equation
#print axioms source_blank_halts_iff_one_equation
end BB6.Agent1Unified

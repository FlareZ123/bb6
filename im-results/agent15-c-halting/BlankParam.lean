import BlankHalting
import SectionParam
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Blank-origin Machine C stopping is exactly reachability of the two
    closed-form dyadic parameter families; the zero-pair is impossible. -/
theorem blank_halts_iff_two_parametric_families :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k, BB6.Agent8Section.run secNext time (some (5,1))=some(a,k) ∧
      ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3)) ∨
       (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3))) := by
  rw [blank_halts_iff_arithmetic]
  constructor
  · rintro ⟨time,hstop⟩
    obtain ⟨t,s,hr,hs⟩ := (run_none_iff_guard secNext (5,1)).mp ⟨time,hstop⟩
    rcases s with ⟨a,k⟩
    have hk := BB6Agent38.blank_section_positive t a k hr
    rcases (section_halts_iff_parametric a k).mp hs with h0|h1|h2
    · omega
    · exact ⟨t,a,k,hr,Or.inl h1⟩
    · exact ⟨t,a,k,hr,Or.inr h2⟩
  · rintro ⟨time,a,k,hr,h⟩
    have hs : secNext (a,k)=none :=
      (section_halts_iff_parametric a k).mpr (Or.inr h)
    exact (run_none_iff_guard secNext (5,1)).mpr ⟨time,(a,k),hr,hs⟩

#print axioms blank_halts_iff_two_parametric_families
end BB6.Agent15

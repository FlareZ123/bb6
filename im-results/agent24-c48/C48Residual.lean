import C48Depth
import BlankParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- The exact blank-origin Machine C halting criterion with every
    one-left gateway indexed by m=424 (mod 1024) removed. The odd-left
    branch is preserved verbatim from the original two-family theorem. -/
theorem blank_halts_iff_without_depth424 :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧ m%1024≠424) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3))) := by
  rw [BB6.Agent15.blank_halts_iff_two_parametric_families]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq⟩ | h2
    · subst a
      have hn : m%1024≠424 := by
        intro hm
        exact blank_no_low_halt_depth424 m k hm heq ⟨time,hr⟩
      exact ⟨time,1,k,hr,Or.inl ⟨rfl,m,heq,hn⟩⟩
    · exact ⟨time,a,k,hr,Or.inr h2⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,hn⟩ | h2
    · exact ⟨time,a,k,hr,Or.inl ⟨ha,m,heq⟩⟩
    · exact ⟨time,a,k,hr,Or.inr h2⟩

#print axioms blank_halts_iff_without_depth424
end BB6.Agent46

import C16Depth
import C48Residual
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- The original Machine C blank-origin stopping criterion with both
    distinct low-family infinite depth residue classes removed. -/
theorem blank_halts_iff_without_depth424_4008 :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧
            m%1024≠424 ∧ m%4096≠4008) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3))) := by
  rw [blank_halts_iff_without_depth424]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,hn⟩ | h2
    · subst a
      have hn2 : m%4096≠4008 := by
        intro hm
        exact blank_no_low_halt_depth4008 m k hm heq ⟨time,hr⟩
      exact ⟨time,1,k,hr,Or.inl ⟨rfl,m,heq,hn,hn2⟩⟩
    · exact ⟨time,a,k,hr,Or.inr h2⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,hn,hn2⟩ | h2
    · exact ⟨time,a,k,hr,Or.inl ⟨ha,m,heq,hn⟩⟩
    · exact ⟨time,a,k,hr,Or.inr h2⟩

#print axioms blank_halts_iff_without_depth424_4008
end BB6.Agent46

import UniformS25Reach
import C16Residual
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Exact original Machine C halting criterion after removal of a third
    authenticated blank-unreachable infinite low-family depth class. -/
theorem blank_halts_iff_without_depth424_4008_30632 :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧
            m%1024≠424 ∧ m%4096≠4008 ∧ m%32768≠30632) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3))) := by
  rw [blank_halts_iff_without_depth424_4008]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,hn,hn2⟩ | h2
    · subst a
      have hn3 : m%32768≠30632 := by
        intro hm
        exact blank_no_low_halt_depth30632 m k hm heq ⟨time,hr⟩
      exact ⟨time,1,k,hr,Or.inl ⟨rfl,m,heq,hn,hn2,hn3⟩⟩
    · exact ⟨time,a,k,hr,Or.inr h2⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,hn,hn2,hn3⟩ | h2
    · exact ⟨time,a,k,hr,Or.inl ⟨ha,m,heq,hn,hn2⟩⟩
    · exact ⟨time,a,k,hr,Or.inr h2⟩

#print axioms blank_halts_iff_without_depth424_4008_30632
end BB6.Agent46

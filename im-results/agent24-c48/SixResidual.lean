import UniformS25Residual
import S5Reach
import OneTenGate
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Exact original-blank Machine C halting criterion after adding the
    broad six-residue inverse sieve to the previously certified three
    low-family exclusions. This is an iff, with the entire authentic
    high stopping family preserved unchanged. -/
theorem blank_halts_iff_six_low_depth_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧
            m%1024≠424 ∧ m%4096≠4008 ∧ m%32768≠30632 ∧
            m%16≠14 ∧ m%64≠38 ∧ m%16384≠5032) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3))) := by
  rw [blank_halts_iff_without_depth424_4008_30632]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,hn,hn2,hn3⟩ | h2
    · subst a
      have hn4 : m%16≠14 := by
        intro hm
        exact blank_no_low_halt_depth14 m k hm heq ⟨time,hr⟩
      have hn5 : m%64≠38 := by
        intro hm
        exact blank_no_low_halt_depth38 m k hm heq ⟨time,hr⟩
      have hn6 : m%16384≠5032 := by
        intro hm
        exact blank_no_low_halt_depth5032 m k hm heq ⟨time,hr⟩
      exact ⟨time,1,k,hr,Or.inl ⟨rfl,m,heq,hn,hn2,hn3,hn4,hn5,hn6⟩⟩
    · exact ⟨time,a,k,hr,Or.inr h2⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,hn,hn2,hn3,_,_,_⟩ | h2
    · exact ⟨time,a,k,hr,Or.inl ⟨ha,m,heq,hn,hn2,hn3⟩⟩
    · exact ⟨time,a,k,hr,Or.inr h2⟩

#print axioms blank_halts_iff_six_low_depth_sieve
end BB6.Agent46

import MixedHighResidual
import MixedLowFour
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- All three independently source-certified infinite Machine C stopping
    exclusions are consumed in one exact authentic blank halting iff:
    the entire low depth m≡4 (mod8) and two disjoint high parameter
    cylinders, including the m=1 high continuation. -/
theorem blank_halts_iff_mixed_low_high_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧ m%8≠4) ∨
         (∃ j m, a=2*j+3 ∧
            k+j+3*m+5=2^(2*m+2)*(j+3) ∧
            ¬ (4≤m ∧
                ((m%4=0 ∧ (j+m)%32=26) ∨
                 (m%4=1 ∧ (j+m)%32=2))) ∧
            ¬ (m=1 ∧ j%32=1))) := by
  rw [blank_halts_iff_mixed_high_sieve]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq⟩ | high
    · have hn : m%8≠4 := by
        intro hm
        subst a
        exact (mixed_low_m_four_mod8_stops_unreachable m k hm heq).2 ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inl ⟨ha,m,heq,hn⟩⟩
    · exact ⟨time,a,k,hr,Or.inr high⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,_⟩ | high
    · exact ⟨time,a,k,hr,Or.inl ⟨ha,m,heq⟩⟩
    · exact ⟨time,a,k,hr,Or.inr high⟩

#print axioms blank_halts_iff_mixed_low_high_sieve
end BB6.Agent3

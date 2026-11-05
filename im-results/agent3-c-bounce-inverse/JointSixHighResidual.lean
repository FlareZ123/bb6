import JointResidual
import MixedHighOneMod4Seven
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Source-exact authentic blank halting iff after combining the complete
    Agent24 and Agent3 prior stopping exclusions with the new entire
    high sector m>=5, m%4=1, j=m+7 mod32. The original stopping
    parameters remain unbounded: no global halting decision is asserted. -/
theorem blank_halts_iff_joint_six_high_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧
          m%1024≠424 ∧ m%4096≠4008 ∧ m%32768≠30632 ∧
          m%16≠14 ∧ m%64≠38 ∧ m%16384≠5032 ∧ m%8≠4) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3) ∧
          ¬ (2≤m ∧ j%4=3 ∧ (j+3*m+7)%16=0) ∧
          ¬ (2≤m ∧ j%4=1 ∧ (j+3*m+11)%32=0) ∧
          ¬ (4≤m ∧
              ((m%4=0 ∧ (j+m)%32=26) ∨
               (m%4=1 ∧ (j+m)%32=2))) ∧
          ¬ (m=1 ∧ j%32=1) ∧
          ¬ (2≤m ∧ j%2=1 ∧ (j+3*m+5)%8=0) ∧
          ¬ (5≤m ∧ m%4=1 ∧ j%32=(m+7)%32))) := by
  rw [blank_halts_iff_joint_low_high_sieve]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hlow | ⟨j,m,ha,heq,h1,h2,h3,h4,h5⟩
    · exact ⟨time,a,k,hr,Or.inl hlow⟩
    · have h6 : ¬ (5≤m ∧ m%4=1 ∧ j%32=(m+7)%32) := by
        rintro ⟨hm5,hm,hj⟩
        subst a
        exact (blank_no_high_one_mod4_diff7 j m k hm5 hm hj heq).2
          ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,h1,h2,h3,h4,h5,h6⟩⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hlow | ⟨j,m,ha,heq,h1,h2,h3,h4,h5,_⟩
    · exact ⟨time,a,k,hr,Or.inl hlow⟩
    · exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,h1,h2,h3,h4,h5⟩⟩

#print axioms blank_halts_iff_joint_six_high_sieve
end BB6.Agent3

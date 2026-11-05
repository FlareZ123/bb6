import SevenResidual
import HighOddSix
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Exact original Machine C halting iff after six low-family and two
    independently certified high-family root-obstruction cylinders. -/
theorem blank_halts_iff_eight_part_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧
            m%1024≠424 ∧ m%4096≠4008 ∧ m%32768≠30632 ∧
            m%16≠14 ∧ m%64≠38 ∧ m%16384≠5032) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3) ∧
           ¬ (2≤m ∧ j%4=3 ∧ (j+3*m+7)%16=0) ∧
           ¬ (2≤m ∧ j%4=1 ∧ (j+3*m+11)%32=0))) := by
  rw [blank_halts_iff_seven_part_sieve]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hLow | ⟨j,m,ha,heq,hnot1⟩
    · exact ⟨time,a,k,hr,Or.inl hLow⟩
    · have hnot2 : ¬ (2≤m ∧ j%4=1 ∧ (j+3*m+11)%32=0) := by
        rintro ⟨hm,hj,hmod⟩
        subst a
        exact blank_no_high_halt_mod32pair j m k hm hj hmod heq ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,hnot1,hnot2⟩⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hLow | ⟨j,m,ha,heq,hnot1,_⟩
    · exact ⟨time,a,k,hr,Or.inl hLow⟩
    · exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,hnot1⟩⟩

#print axioms blank_halts_iff_eight_part_sieve
end BB6.Agent46

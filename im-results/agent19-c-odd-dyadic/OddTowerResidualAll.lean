import OddTowerSource
import EightResidual
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Tower

/-- Exact authentic blank halting criterion retaining only stopping
    configurations outside the new all-exponent forbidden dyadic family. -/
theorem blank_halts_iff_all_dyadic_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧
            m%1024≠424 ∧ m%4096≠4008 ∧ m%32768≠30632 ∧
            m%16≠14 ∧ m%64≠38 ∧ m%16384≠5032) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3) ∧
           ¬ (2≤m ∧ j%4=3 ∧ (j+3*m+7)%16=0) ∧
           ¬ (2≤m ∧ j%4=1 ∧ (j+3*m+11)%32=0) ∧
           (∀ n, ¬ (n+4≤2*m+2 ∧
             (j+3*m+3)%2^(n+4)=2^(n+2) ∧
             (2*j+3)%8=(if n%2=0 then 7 else 3))))) := by
  rw [BB6.Agent46.blank_halts_iff_eight_part_sieve]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hLow | ⟨j,m,ha,heq,hnot1,hnot2⟩
    · exact ⟨time,a,k,hr,Or.inl hLow⟩
    · have hall : ∀ n, ¬ (n+4≤2*m+2 ∧
          (j+3*m+3)%2^(n+4)=2^(n+2) ∧
          (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
        intro n
        rintro ⟨hm,hpair,hj⟩
        subst a
        exact blank_no_high_stop_all_depth n j m k hm hpair hj heq ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,hnot1,hnot2,hall⟩⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hLow | ⟨j,m,ha,heq,hnot1,hnot2,_⟩
    · exact ⟨time,a,k,hr,Or.inl hLow⟩
    · exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,hnot1,hnot2⟩⟩

#print axioms blank_halts_iff_all_dyadic_sieve
end BB6.Agent19Tower

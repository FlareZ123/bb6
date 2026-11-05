import EightResidual
import MixedLowFour
import MixedHighOne
import MixedHighEightSharp
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Joint lossless Machine C genuine-blank halting criterion consuming
    Agent24's six authenticated low and two high exclusions together with
    Agent3's all-m=4 mod8 low and three high exclusions. Each gate is a
    necessary condition for a reachable source-authentic stopping state. -/
theorem blank_halts_iff_joint_low_high_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1)) = some (a,k) ∧
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
          ¬ (2≤m ∧ j%2=1 ∧ (j+3*m+5)%8=0))) := by
  rw [BB6.Agent46.blank_halts_iff_eight_part_sieve]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,h1,h2,h3,h4,h5,h6⟩ |
      ⟨j,m,ha,heq,hnot1,hnot2⟩
    · have h7 : m%8≠4 := by
        intro hm
        subst a
        exact (mixed_low_m_four_mod8_stops_unreachable m k hm heq).2 ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inl ⟨ha,m,heq,h1,h2,h3,h4,h5,h6,h7⟩⟩
    · have hnot3 : ¬ (4≤m ∧
            ((m%4=0 ∧ (j+m)%32=26) ∨
             (m%4=1 ∧ (j+m)%32=2))) := by
        rintro ⟨hm,hpair⟩
        subst a
        exact mixed_high_m04_pair_unreachable j m k hm hpair heq ⟨time,hr⟩
      have hnot4 : ¬ (m=1 ∧ j%32=1) := by
        rintro ⟨hm,hj⟩
        have hjform : j=32*(j/32)+1 := by omega
        have hkform : k=480*(j/32)+55 := by
          rw [hm,hjform] at heq
          have h16 : (2:Nat)^(2*1+2)=16 := by decide
          rw [h16] at heq
          omega
        have haform : 2*j+3=64*(j/32)+5 := by omega
        subst a
        rw [haform,hkform] at hr
        exact mixed_high_m1_j_one_mod32_unreachable (j/32) ⟨time,hr⟩
      have hnot5 : ¬ (2≤m ∧ j%2=1 ∧ (j+3*m+5)%8=0) := by
        rintro ⟨hm,hj,hres⟩
        subst a
        exact (mixed_high_even_eight_sharp j m k hm hj hres heq).2.2.2
          ⟨time,hr⟩
      exact ⟨time,a,k,hr,
        Or.inr ⟨j,m,ha,heq,hnot1,hnot2,hnot3,hnot4,hnot5⟩⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,h1,h2,h3,h4,h5,h6,_⟩ |
      ⟨j,m,ha,heq,hnot1,hnot2,_,_,_⟩
    · exact ⟨time,a,k,hr,Or.inl ⟨ha,m,heq,h1,h2,h3,h4,h5,h6⟩⟩
    · exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,hnot1,hnot2⟩⟩

#print axioms blank_halts_iff_joint_low_high_sieve
end BB6.Agent3

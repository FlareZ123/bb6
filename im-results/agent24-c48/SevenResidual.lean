import HighOddTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Lossless exact stopping criterion for the authentic Machine C blank
    computation. Both disjoint low-depth and newly excluded two-parameter
    high-family congruences are excised, preserving full iff. -/
theorem blank_halts_iff_seven_part_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧
            m%1024≠424 ∧ m%4096≠4008 ∧ m%32768≠30632 ∧
            m%16≠14 ∧ m%64≠38 ∧ m%16384≠5032) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3) ∧
           ¬ (2≤m ∧ j%4=3 ∧ (j+3*m+7)%16=0))) := by
  rw [blank_halts_iff_six_low_depth_sieve]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hLow | ⟨j,m,ha,heq⟩
    · exact ⟨time,a,k,hr,Or.inl hLow⟩
    · have hn : ¬ (2≤m ∧ j%4=3 ∧ (j+3*m+7)%16=0) := by
        rintro ⟨hm,hj,hmod⟩
        subst a
        exact blank_no_high_halt_mod16pair j m k hm hj hmod heq ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,hn⟩⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hLow | ⟨j,m,ha,heq,_⟩
    · exact ⟨time,a,k,hr,Or.inl hLow⟩
    · exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq⟩⟩

#print axioms blank_halts_iff_seven_part_sieve
end BB6.Agent46

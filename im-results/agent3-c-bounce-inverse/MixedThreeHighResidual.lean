import MixedFullResidual
import MixedHighEightSharp
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Authentic blank-halting iff after new complete low m=4 (mod8)
    root exclusion and three independent high-family root exclusions.
    This theorem still leaves infinitely many low and high candidates,
    so it is a sharp refinement of the original halting criterion only. -/
theorem blank_halts_iff_mixed_three_high_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧ m%8≠4) ∨
         (∃ j m, a=2*j+3 ∧
            k+j+3*m+5=2^(2*m+2)*(j+3) ∧
            ¬ (4≤m ∧
                ((m%4=0 ∧ (j+m)%32=26) ∨
                 (m%4=1 ∧ (j+m)%32=2))) ∧
            ¬ (m=1 ∧ j%32=1) ∧
            ¬ (2≤m ∧ j%2=1 ∧ (j+3*m+5)%8=0))) := by
  rw [blank_halts_iff_mixed_low_high_sieve]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hlow | ⟨j,m,ha,hstop,hn1,hn2⟩
    · exact ⟨time,a,k,hr,Or.inl hlow⟩
    · have hn3 : ¬ (2≤m ∧ j%2=1 ∧ (j+3*m+5)%8=0) := by
        rintro ⟨hm,hj,hres⟩
        subst a
        exact (mixed_high_even_eight_sharp j m k hm hj hres hstop).2.2.2
          ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,hstop,hn1,hn2,hn3⟩⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hlow | ⟨j,m,ha,hstop,hn1,hn2,_⟩
    · exact ⟨time,a,k,hr,Or.inl hlow⟩
    · exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,hstop,hn1,hn2⟩⟩

#print axioms blank_halts_iff_mixed_three_high_sieve
end BB6.Agent3

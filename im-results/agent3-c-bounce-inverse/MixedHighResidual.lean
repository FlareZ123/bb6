import MixedHighBoth
import MixedHighOne
import BlankParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Exact all-time genuine blank Machine C halting iff, with both new
    infinite high stopping parameter cylinders removed and the low
    stopping family retained without change. m=1 is handled separately. -/
theorem blank_halts_iff_mixed_high_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3)) ∨
         (∃ j m, a=2*j+3 ∧
            k+j+3*m+5=2^(2*m+2)*(j+3) ∧
            ¬ (4≤m ∧
                ((m%4=0 ∧ (j+m)%32=26) ∨
                 (m%4=1 ∧ (j+m)%32=2))) ∧
            ¬ (m=1 ∧ j%32=1))) := by
  rw [BB6.Agent15.blank_halts_iff_two_parametric_families]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hlow | ⟨j,m,ha,hstop⟩
    · exact ⟨time,a,k,hr,Or.inl hlow⟩
    · have hnot : ¬ (4≤m ∧
                  ((m%4=0 ∧ (j+m)%32=26) ∨
                   (m%4=1 ∧ (j+m)%32=2))) := by
        rintro ⟨hm,hpair⟩
        subst a
        exact mixed_high_m04_pair_unreachable j m k hm hpair hstop
          ⟨time,hr⟩
      have hnot1 : ¬ (m=1 ∧ j%32=1) := by
        rintro ⟨hm,hj⟩
        have hjform : j=32*(j/32)+1 := by omega
        have hkform : k=480*(j/32)+55 := by
          rw [hm,hjform] at hstop
          norm_num at hstop
          omega
        have haform : 2*j+3=64*(j/32)+5 := by omega
        subst a
        rw [haform,hkform] at hr
        exact mixed_high_m1_j_one_mod32_unreachable (j/32) ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,hstop,hnot,hnot1⟩⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hlow | ⟨j,m,ha,hstop,_,_⟩
    · exact ⟨time,a,k,hr,Or.inl hlow⟩
    · exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,hstop⟩⟩

#print axioms blank_halts_iff_mixed_high_sieve
end BB6.Agent3

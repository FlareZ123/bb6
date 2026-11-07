import HighAllPhases
import BlankParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Exactly the two complementary all-depth high stopping parameter
    classes excluded by the source-faithful exceptional inverse cone. -/
def allPhaseExcluded (j m : Nat) : Prop :=
    ∃ r, 8≤r ∧ r+4≤2*m+2 ∧
      ((j%16=(2*r)%16 ∧ (j+3*m+3)%2^(r+4)=9*2^r) ∨
       (j%16=(12+2*r)%16 ∧ (j+3*m+3)%2^(r+4)=13*2^r))

/-- Exact original-blank Machine C halting iff retaining both complete
    source stopping families, with the new all-depth forbidden high
    subfamilies excised without any finite run-time cutoff. This does not
    resolve the remaining existential halting question. -/
theorem blank_halts_iff_all_phase_high_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3)) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3) ∧
           ¬allPhaseExcluded j m)) := by
  rw [BB6.Agent15.blank_halts_iff_two_parametric_families]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hlow | ⟨j,m,ha,heq⟩
    · exact ⟨time,a,k,hr,Or.inl hlow⟩
    · have hnot : ¬allPhaseExcluded j m := by
        rintro ⟨r,hr8,hwidth,hbranch⟩
        subst a
        rcases hbranch with ⟨hj,hmod⟩ | ⟨hj,hmod⟩
        · exact high_all_phase_A_no_blank r j m k hr8 hwidth hj hmod heq ⟨time,hr⟩
        · exact high_all_phase_B_no_blank r j m k hr8 hwidth hj hmod heq ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,hnot⟩⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hlow | ⟨j,m,ha,heq,_⟩
    · exact ⟨time,a,k,hr,Or.inl hlow⟩
    · exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq⟩⟩

#print axioms blank_halts_iff_all_phase_high_sieve
end BB6.Agent46

import CThirdSixSevenPullback
import S3LatestPredicate
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent12SevenLatest

/-- Latest exact high predicate, strengthened by Agent 12's third
    strict sixth/seventh source-image cylinder. -/
def highAllowedA12 (j m : Nat) : Prop :=
  BB6.Agent19S3Latest.highAllowed j m ∧
  ¬(j%512=319 ∧ (3*m+71*j+17161)%65536=0)

/-- Exact genuine-blank Machine C halting iff after removing the third
    strict sixth/seventh high-stop cylinder from the latest exact
    six-sector + m=0 + s3 criterion. The low branch and fixed-target
    decision procedure are unchanged. -/
theorem blank_halts_iff_after_a12 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedA12 j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent19S3Latest.blank_halts_iff_s3_after_s293]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff
          (2*j+3) k).mp hroot
      have hnot :
          ¬(j%512=319 ∧ (3*m+71*j+17161)%65536=0) := by
        rintro ⟨hjmod,hcong⟩
        obtain ⟨time,hrun⟩ := hreach
        exact BB6.Agent12SevenPullback.blank_ne_parameter_congruence_a12
          j m time hjmod hcong (by simpa [k] using hrun)
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- Every parameter in the new affine cylinder is removed by the
    strengthened exact high predicate. -/
theorem parameter_cylinder_removed_a12 (j m : Nat)
    (hj : j%512=319)
    (hcong : (3*m+71*j+17161)%65536=0) :
    ¬ highAllowedA12 j m := by
  intro h
  exact h.2 ⟨hj,hcong⟩

#print axioms blank_halts_iff_after_a12
#print axioms parameter_cylinder_removed_a12

end BB6.Agent12SevenLatest

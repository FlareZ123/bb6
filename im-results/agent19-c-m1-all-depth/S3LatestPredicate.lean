import CSixSeventhSixAll
import CThreeDiagonalM0SumZeroS293Full
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19S3Latest

/-- The latest six-sector high predicate, including the two sum-zero
    m=0 rays and the S293 m=0 ray, strengthened by the independent
    second strict sixth/seventh image cylinder. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11M0SumZeroS293Full.highAllowed j m ∧
  ¬(j%512=319 ∧ (3*m+7*j+14025)%16384=0)

/-- Every member of the s3 image pullback survives the latest
    pre-existing six-sector and m=0 high restrictions. The three
    later m=0 guards are vacuous because this cylinder has m≥7
    (in fact the exact pullback forces m≥42). -/
theorem prior_latest_admits_s3_image_family (j m u v : Nat)
    (hm7 : 7≤m)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v)
    (hsector : (u+v)%16=(15+4*u)%16) :
    BB6.Agent11M0SumZeroS293Full.highAllowed j m := by
  have hprior :=
    BB6.Agent4SevenSixAll.prior_six_all_admits_s3_image_family
      j m u v hm7 hj hk hsector
  have hsum : BB6.Agent11M0SumZeroAll.highAllowed j m := by
    unfold BB6.Agent11M0SumZeroAll.highAllowed
    exact ⟨hprior,by omega,by omega⟩
  unfold BB6.Agent11M0SumZeroS293Full.highAllowed
  exact ⟨hsum,by omega⟩

/-- The new parameter-only s3 exclusion is strict relative to the
    latest pre-existing high predicate, not a restatement of an
    earlier m=0 guard. -/
theorem s3_family_removed (j m : Nat)
    (hj : j%512=319)
    (hcong : (3*m+7*j+14025)%16384=0) :
    ¬highAllowed j m := by
  intro h
  exact h.2 ⟨hj,hcong⟩

/-- Exact genuine-blank Machine C halting iff after composing the
    s3 all-time strict-image exclusion with the latest six-sector
    criterion, including the later m=0 sum-zero and S293 exclusions. -/
theorem blank_halts_iff_s3_after_s293 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11M0SumZeroS293Full.blank_halts_iff_six_mzero_sumzero_s293]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff
          (2*j+3) k).mp hroot
      have hnot :
          ¬(j%512=319 ∧ (3*m+7*j+14025)%16384=0) := by
        rintro ⟨hjmod,hcong⟩
        obtain ⟨time,hrun⟩ := hreach
        exact BB6.Agent4SevenC58.blank_ne_s3_parameter_congruence
          j m time hjmod hcong (by simpa [k] using hrun)
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms prior_latest_admits_s3_image_family
#print axioms s3_family_removed
#print axioms blank_halts_iff_s3_after_s293

end BB6.Agent19S3Latest

import CSixSeventhC58
import CThreeSixAllCriterion
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4SevenSixAll

/-- The stopping equation and the s3 image coordinate force the
    previously added odd-diagonal residue to be m=10 (mod 32). -/
private theorem s3_parameter_m32 (j m u v : Nat)
    (hm7 : 7≤m)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v) :
    m%32=10 := by
  have hpow32 : 32 ∣ (2:Nat)^(2*m+2) := by
    have h := Nat.pow_dvd_pow 2 (by omega : 5≤2*m+2)
    simpa only [show (2:Nat)^5=32 by decide] using h
  have hprod32 : 32 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow32 with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hbound : j+3*m+5 ≤ (2:Nat)^(2*m+2)*(j+3) := by
    have hP : 4*m+4 ≤ (2:Nat)^(2*m+2) :=
      BB6.Agent29New.power_linear_bound m
    have hp : 1 ≤ (2:Nat)^(2*m+2) :=
      Nat.pow_pos (by decide)
    have hjle : j ≤ (2:Nat)^(2*m+2)*j := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
    have hmle : 3*m+5 ≤ 3*(2:Nat)^(2*m+2) := by omega
    rw [Nat.mul_add]
    omega
  have hstop : (574+1024*v)+j+3*m+5 =
      (2:Nat)^(2*m+2)*(j+3) := by
    rw [← hk]
    exact Nat.sub_add_cancel hbound
  have hzero : ((574+1024*v)+j+3*m+5)%32=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod32
  rw [hj] at hzero
  omega

/-- The affine s3 target itself is outside all six recursive forced
    inverse gates: its right coordinate is even, its sum is 7 mod 8,
    and its left coordinate is 1 mod 16. Hence the six-sector filter
    returns false on the whole image family. -/
private theorem s3_six_forced_admitted (u v : Nat) :
    BB6.Agent11SixForced.sixForcedExcluded
      (641+1024*u) (574+1024*v)=false := by
  have hx2 : (641+1024*u)%2=1 := by omega
  have hx16 : (641+1024*u)%16=1 := by omega
  have hy2 : (574+1024*v)%2=0 := by omega
  have hsum4 : (641+1024*u+574+1024*v)%4=3 := by omega
  have hsum8 : (641+1024*u+574+1024*v)%8=7 := by omega
  have hnotOdd :
      ¬BB6.Agent3.oddLowGate (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent3.oddLowGate, hy2] at h
  have hnotSeven :
      ¬BB6.Agent3.evenSevenGate (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent3.evenSevenGate, hx2, hy2] at h
  have hnotAffine :
      ¬BB6.Agent3.evenAffineGate (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent3.evenAffineGate, hsum4] at h
  have hnotSix :
      ¬BB6.Agent46.sixEvenRightGate (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent46.sixEvenRightGate, hsum8] at h
  have hnotValSix :
      ¬BB6.Agent3ValSix.valSixGate (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent3ValSix.valSixGate, hx16] at h
  have hnotEvenOdd :
      ¬BB6.Agent11SixForced.evenOddFourGate
        (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent11SixForced.evenOddFourGate, hx2, hy2] at h
  have hnorm :
      BB6.Agent11SixForced.sixForcedNormalize
        (641+1024*u) (574+1024*v) =
        (641+1024*u,574+1024*v) := by
    simp [BB6.Agent11SixForced.sixForcedNormalize,
      hnotOdd,hnotSeven,hnotAffine,hnotSix,hnotValSix,hnotEvenOdd]
  simp [BB6.Agent11SixForced.sixForcedExcluded, hnorm, hy2]

/-- Every member of the second strict sixth/seventh image family also
    survives the *latest* merged C58, odd-diagonal, m=0, and six-sector
    high predicate. The extra diagonal misses because m=10 mod 32 while
    (j+25)=24 mod 32; the m=0 guards are vacuous; the six-sector
    normalizer takes no edge on (641+1024u,574+1024v). -/
theorem prior_six_all_admits_s3_image_family (j m u v : Nat)
    (hm7 : 7≤m)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v)
    (hsector : (u+v)%16=(15+4*u)%16) :
    BB6.Agent11SixAll.highAllowed j m := by
  have hlate :=
    BB6.Agent4SevenC58.prior_latefast_admits_s3_image_family
      j m u v hm7 hj hk hsector
  have hbase : BB6.Agent11LateFastWrapper.highAllowed j m := hlate.1
  have hm32 : m%32=10 := s3_parameter_m32 j m u v hm7 hj hk
  have hdiagLate : BB6.Agent11DiagonalLate.highAllowed j m := by
    refine ⟨hbase,?_⟩
    rintro ⟨hm2,hjodd,hmod⟩
    have hjplus : (j+25)%32=24 := by rw [hj]; omega
    omega
  have hdiagM0 : BB6.Agent11DiagonalM0.highAllowed j m := by
    refine ⟨hdiagLate,?_⟩
    rintro ⟨hmzero,hj128⟩
    omega
  have hdiagDeep : BB6.Agent11M0DeepFull.highAllowed j m := by
    refine ⟨hdiagM0,?_⟩
    rintro ⟨hmzero,hj2048⟩
    omega
  have hforced :
      BB6.Agent11SixForced.sixForcedExcluded (2*j+3)
        (2^(2*m+2)*(j+3)-(j+3*m+5))=false := by
    rw [hk]
    have hx : 2*j+3=641+1024*u := by omega
    rw [hx]
    exact s3_six_forced_admitted u v
  change BB6.Agent11M0DeepFull.highAllowed j m ∧
    BB6.Agent11SixForced.sixForcedExcluded (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5))=false
  exact ⟨hdiagDeep,hforced⟩

/-- Strengthen the latest exact six-sector halting criterion by
    removing the second strict s3 image family in its exact parameter-only
    congruence form, while retaining the exact low branch and fixed-target test. -/
def highAllowedAllS3Six (j m : Nat) : Prop :=
  BB6.Agent11SixAll.highAllowed j m ∧
  ¬(j%512=319 ∧ (3*m+7*j+14025)%16384=0)

theorem blank_halts_iff_six_both_s3 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedAllS3Six j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11SixAll.blank_halts_iff_six_both]
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
        obtain ⟨u,v,hj,hk,hsector⟩ :=
          (BB6.Agent4SevenC58.s3_image_pullback_iff_congruence j m).2
            ⟨hjmod,hcong⟩
        obtain ⟨time,hrun⟩ := hreach
        have hblank :=
          BB6.Agent4Seven.blank_ne_six_seven_band_s3 u v time hsector
        have hx : 2*j+3=641+1024*u := by omega
        apply hblank
        rw [hx,hk] at hrun
        exact hrun
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- The whole s3 family is a genuine additional exclusion from the
    latest exact high predicate, not merely a restatement of an older
    sieve: every member is admitted before the new source-root filter. -/
theorem s3_image_family_removed_from_six_all (j m u v : Nat)
    (hm7 : 7≤m)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v)
    (hsector : (u+v)%16=(15+4*u)%16) :
    ¬highAllowedAllS3Six j m := by
  intro h
  have hcong :=
    (BB6.Agent4SevenC58.s3_image_pullback_iff_congruence j m).1
      ⟨u,v,hj,hk,hsector⟩
  exact h.2 hcong

#print axioms prior_six_all_admits_s3_image_family
#print axioms blank_halts_iff_six_both_s3
#print axioms s3_image_family_removed_from_six_all

end BB6.Agent4SevenSixAll

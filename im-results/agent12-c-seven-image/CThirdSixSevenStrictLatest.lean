import CThirdSixSevenLatest
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent12SevenStrictLatest

/-- Every target of the affine band itself is admitted by the recursive
    six-source normalizer: no forced inverse gate fires. -/
private theorem six_forced_admitted_a12 (u v : Nat) :
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
    simp [BB6.Agent3.oddLowGate,hy2] at h
  have hnotSeven :
      ¬BB6.Agent3.evenSevenGate (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent3.evenSevenGate,hx2,hy2] at h
  have hnotAffine :
      ¬BB6.Agent3.evenAffineGate (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent3.evenAffineGate,hsum4] at h
  have hnotSix :
      ¬BB6.Agent46.sixEvenRightGate (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent46.sixEvenRightGate,hsum8] at h
  have hnotValSix :
      ¬BB6.Agent3ValSix.valSixGate (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent3ValSix.valSixGate,hx16] at h
  have hnotEvenOdd :
      ¬BB6.Agent11SixForced.evenOddFourGate
        (641+1024*u) (574+1024*v) := by
    intro h
    simp [BB6.Agent11SixForced.evenOddFourGate,hx2,hy2] at h
  have hnorm :
      BB6.Agent11SixForced.sixForcedNormalize
        (641+1024*u) (574+1024*v) =
        (641+1024*u,574+1024*v) := by
    simp [BB6.Agent11SixForced.sixForcedNormalize,
      hnotOdd,hnotSeven,hnotAffine,hnotSix,hnotValSix,hnotEvenOdd]
  simp [BB6.Agent11SixForced.sixForcedExcluded,hnorm,hy2]

private theorem new_congruence_forces_m512 (j m : Nat)
    (hj : j%512=319)
    (hnew : (3*m+71*j+17161)%65536=0) :
    m%512=42 := by
  have hdiv : 512 ∣ 65536 := by decide
  have hmod : (3*m+71*j+17161)%512=0 := by
    calc
      (3*m+71*j+17161)%512 =
          ((3*m+71*j+17161)%65536)%512 := by
        symm
        exact Nat.mod_mod_of_dvd _ hdiv
      _ = 0%512 := by rw [hnew]
      _ = 0 := by decide
  omega

private theorem new_disjoint_from_s3 (j m : Nat)
    (hj : j%512=319)
    (hnew : (3*m+71*j+17161)%65536=0) :
    ¬(3*m+7*j+14025)%16384=0 := by
  intro hs3
  have hdiv : 16384 ∣ 65536 := by decide
  have hnew16 : (3*m+71*j+17161)%16384=0 := by
    calc
      (3*m+71*j+17161)%16384 =
          ((3*m+71*j+17161)%65536)%16384 := by
        symm
        exact Nat.mod_mod_of_dvd _ hdiv
      _ = 0%16384 := by rw [hnew]
      _ = 0 := by decide
  omega

/-- The complete third image family survives every previously integrated
    high restriction: C58, arbitrary-depth late gates, the old diagonal,
    all m=0 rays, the recursive six-source normalizer, and the prior s3
    sixth/seventh cylinder. Hence the new exclusion is genuinely strict. -/
theorem prior_latest_admits_a12_image_family (j m u v : Nat)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v)
    (hsector : (29*u+v)%64=38) :
    BB6.Agent19S3Latest.highAllowed j m := by
  have hnew :=
    (BB6.Agent12SevenPullback.image_pullback_iff_congruence_a12 j m).1
      ⟨u,v,hj,hk,hsector⟩
  have hjmod : j%512=319 := hnew.1
  have hcong := hnew.2
  have hm512 : m%512=42 :=
    new_congruence_forces_m512 j m hjmod hcong
  have hm42 : 42≤m := by
    have hle := Nat.mod_le m 512
    omega
  have hbase : BB6.Agent11LateFastWrapper.highAllowed j m :=
    BB6.Agent4SevenC58.prior_latefast_admits_base_residue
      j m (by omega) hjmod hm512
  have hdiagLate : BB6.Agent11DiagonalLate.highAllowed j m := by
    refine ⟨hbase,?_⟩
    rintro ⟨hm2,hjodd,hdiag⟩
    have hj32 : j%32=31 := by omega
    have hm32 : m%32=10 := by omega
    omega
  have hdiagM0 : BB6.Agent11DiagonalM0.highAllowed j m := by
    refine ⟨hdiagLate,?_⟩
    rintro ⟨hm0,_⟩
    omega
  have hdeep : BB6.Agent11M0DeepFull.highAllowed j m := by
    refine ⟨hdiagM0,?_⟩
    rintro ⟨hm0,_⟩
    omega
  have hforced :
      BB6.Agent11SixForced.sixForcedExcluded (2*j+3)
        (2^(2*m+2)*(j+3)-(j+3*m+5))=false := by
    rw [hk]
    have hx : 2*j+3=641+1024*u := by omega
    rw [hx]
    exact six_forced_admitted_a12 u v
  have hsix : BB6.Agent11SixAll.highAllowed j m := by
    change BB6.Agent11M0DeepFull.highAllowed j m ∧
      BB6.Agent11SixForced.sixForcedExcluded (2*j+3)
        (2^(2*m+2)*(j+3)-(j+3*m+5))=false
    exact ⟨hdeep,hforced⟩
  have hsumzero : BB6.Agent11M0SumZeroAll.highAllowed j m := by
    unfold BB6.Agent11M0SumZeroAll.highAllowed
    exact ⟨hsix,by omega,by omega⟩
  have hs293 : BB6.Agent11M0SumZeroS293Full.highAllowed j m := by
    unfold BB6.Agent11M0SumZeroS293Full.highAllowed
    exact ⟨hsumzero,by omega⟩
  have hnots3 :
      ¬(j%512=319 ∧ (3*m+7*j+14025)%16384=0) := by
    rintro ⟨_,hs3⟩
    exact new_disjoint_from_s3 j m hjmod hcong hs3
  unfold BB6.Agent19S3Latest.highAllowed
  exact ⟨hs293,hnots3⟩

/-- Strictness relative to the actual previous latest high predicate. -/
theorem a12_image_family_strict_latest (j m u v : Nat)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v)
    (hsector : (29*u+v)%64=38) :
    BB6.Agent19S3Latest.highAllowed j m ∧
      ¬BB6.Agent12SevenLatest.highAllowedA12 j m := by
  have hprior :=
    prior_latest_admits_a12_image_family j m u v hj hk hsector
  have hnew :=
    (BB6.Agent12SevenPullback.image_pullback_iff_congruence_a12 j m).1
      ⟨u,v,hj,hk,hsector⟩
  refine ⟨hprior,?_⟩
  intro h
  exact h.2 hnew

#print axioms prior_latest_admits_a12_image_family
#print axioms a12_image_family_strict_latest

end BB6.Agent12SevenStrictLatest

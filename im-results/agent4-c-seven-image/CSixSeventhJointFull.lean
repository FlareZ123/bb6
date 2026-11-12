import CSixSeventhRoot
import ValSixJointFull
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4SevenJointFull

/-- The high stopping equation forces m=42 modulo 128 on the s3
    image family. This supplies all smaller residue facts used below. -/
private theorem s3_parameter_m128 (j m u v : Nat)
    (hm7 : 7≤m)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v) :
    m%128=42 := by
  have hpow128 : 128 ∣ (2:Nat)^(2*m+2) := by
    have h := Nat.pow_dvd_pow 2 (by omega : 7≤2*m+2)
    simpa only [show (2:Nat)^7=128 by decide] using h
  have hprod128 : 128 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow128 with ⟨q,hq⟩
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
  have hzero : ((574+1024*v)+j+3*m+5)%128=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod128
  rw [hj] at hzero
  omega

/-- The second strict sixth/seventh image family survives every
    restriction in the currently integrated Agent 3/11/19/29 high
    predicate. The only nontrivial high residue is m=42 mod 128. -/
theorem prior_joint_full_admits_s3_image_family (j m u v : Nat)
    (hm7 : 7≤m)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v)
    (hsector : (u+v)%16=(15+4*u)%16) :
    BB6.Agent3ValSix.highAllowedValSixFull j m := by
  have hm128 : m%128=42 := s3_parameter_m128 j m u v hm7 hj hk
  have hm64 : m%64=42 := by omega
  have hm32 : m%32=10 := by omega
  have hm16 : m%16=10 := by omega
  have hm8 : m%8=2 := by omega
  have hm4 : m%4=2 := by omega
  have hj2 : j%2=1 := by rw [hj]; omega
  have hj4 : j%4=3 := by rw [hj]; omega
  have hj8 : j%8=7 := by rw [hj]; omega
  have hj32 : j%32=31 := by rw [hj]; omega
  have hj64 : j%64=63 := by rw [hj]; omega
  have hj128 : j%128=63 := by rw [hj]; omega
  have hx8 : (2*j+3)%8=1 := by rw [hj]; omega
  have hsum16 : (j+3*m+7)%16=4 := by omega
  have hsum8 : (j+3*m+5)%8=2 := by omega
  have hsum64a : (j+3*m+15)%64=12 := by omega
  have hsum64b : (j+3*m+19)%64=16 := by omega
  have hsum128 : (j+3*m)%128=61 := by omega
  have hjm4 : (j+m)%4=1 := by omega
  have hjm16 : (j+m)%16=9 := by omega

  have hjoint : BB6.Agent3.jointHighAllowed j m := by
    change
      ¬(2≤m ∧ j%4=3 ∧ (j+3*m+7)%16=0) ∧
      ¬(2≤m ∧ j%4=1 ∧ (j+3*m+11)%32=0) ∧
      ¬(4≤m ∧
        ((m%4=0 ∧ (j+m)%32=26) ∨
         (m%4=1 ∧ (j+m)%32=2))) ∧
      ¬(m=1 ∧ j%32=1) ∧
      ¬(2≤m ∧ j%2=1 ∧ (j+3*m+5)%8=0)
    refine ⟨?_,?_,?_,?_,?_⟩
    · rintro ⟨hm2,hj4',hmod⟩
      omega
    · rintro ⟨hm2,hj4',hmod⟩
      omega
    · rintro ⟨hm4',hcase⟩
      rcases hcase with hcase | hcase
      · omega
      · omega
    · rintro ⟨hm1,hj32'⟩
      omega
    · rintro ⟨hm2,hj2',hmod⟩
      omega

  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    change BB6.Agent3.jointHighAllowed j m ∧
      ¬(m%32=5 ∧ j%32=12)
    refine ⟨hjoint,?_⟩
    rintro ⟨hm5,hj12⟩
    omega

  have hdyadic :
      ∀ n, ¬(n+4≤2*m+2 ∧
        (j+3*m+3)%2^(n+4)=2^(n+2) ∧
        (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n h
    rcases h with ⟨hn,hmod,hx⟩
    omega

  have hodd1 :
      ¬(2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) := by
    rintro ⟨hm2,hj8',hmod⟩
    omega
  have hodd2 :
      ¬(2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) := by
    rintro ⟨hm2,hj8',hmod⟩
    omega
  have hodd3 :
      ¬(3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) := by
    rintro ⟨hm3,hj8',hmod⟩
    omega
  have hodd4 :
      ¬(3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0) := by
    rintro ⟨hm3,hj8',hmod⟩
    omega
  have h19 : BB6.Agent19Joint.highAllowed j m := by
    change BB6.Agent3.jointHighRectAllowed j m ∧
      (∀ n, ¬(n+4≤2*m+2 ∧
        (j+3*m+3)%2^(n+4)=2^(n+2) ∧
        (2*j+3)%8=(if n%2=0 then 7 else 3))) ∧
      ¬(2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) ∧
      ¬(2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) ∧
      ¬(3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) ∧
      ¬(3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0)
    exact ⟨hrect,hdyadic,hodd1,hodd2,hodd3,hodd4⟩

  have h11 : BB6.Agent11Joint.highAllowed j m := by
    change BB6.Agent19Joint.highAllowed j m ∧
      (j+m)%4≠0 ∧
      ¬(2≤m ∧ (j+m)%16=6 ∧ m%4≠1)
    refine ⟨h19,?_ ,?_⟩
    · omega
    · rintro ⟨hm2,hjm16',hm4ne⟩
      omega

  have h29 : BB6.Agent29Joint.highAllowedPlus j m := by
    change BB6.Agent19Joint.highAllowed j m ∧
      ¬(4≤m ∧ j%8=5 ∧ (j+31)%128=(3*m)%128) ∧
      ¬(4≤m ∧ j%32=17 ∧ (j+31)%128=(3*m)%128) ∧
      ¬(4≤m ∧ j%64=57 ∧ (j+31)%128=(3*m)%128) ∧
      ¬(m%32=6 ∧ (j+51)%256=(9*m)%256)
    refine ⟨h19,?_,?_,?_,?_⟩
    · rintro ⟨hm4',hj8',hmod⟩
      omega
    · rintro ⟨hm4',hj32',hmod⟩
      omega
    · rintro ⟨hm4',hj64',hmod⟩
      omega
    · rintro ⟨hm32',hmod⟩
      omega

  have hvalSix : BB6.Agent3ValSix.highAllowedValSix j m := by
    change BB6.Agent29Joint.highAllowedPlus j m ∧
      ¬(4≤m ∧ m%8=4 ∧ (j+191)%256=(3*m)%256) ∧
      ¬(4≤m ∧ j%128=81 ∧ (j+63)%256=(3*m)%256)
    refine ⟨h29,?_,?_⟩
    · rintro ⟨hm4',hm8',hmod⟩
      omega
    · rintro ⟨hm4',hj128',hmod⟩
      omega

  have hvalSixThree : BB6.Agent3ValSix.highAllowedValSixThree j m := by
    change BB6.Agent3ValSix j m ∧
      ¬(4≤m ∧ j%32=1 ∧ (j+63)%256=(3*m)%256)
    refine ⟨hvalSix,?_⟩
    rintro ⟨hm4',hj32',hmod⟩
    omega

  have h19Five : BB6.Agent19Five.highAllowed j m := by
    change BB6.Agent11Joint.highAllowed j m ∧
      ¬(m%16=10 ∧ (j+3*m+19)%64=0)
    refine ⟨h11,?_⟩
    rintro ⟨hm16',hmod⟩
    omega

  have hfull : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    change BB6.Agent3ValSix.highAllowedValSixThree j m ∧
      BB6.Agent19Five.highAllowed j m ∧
      ¬(j%32=31 ∧ 3≤m ∧ (j+3*m)%128=127) ∧
      ¬(j%8=5 ∧ m%8=4 ∧ (9*j+39)%128=(3*m)%128) ∧
      ¬(m%32=21 ∧ j%32=28) ∧
      (BB6.Agent15.affineNormalize (2*j+3)
        (2^(2*m+2)*(j+3)-(j+3*m+5))).2 ≠ 4
    refine ⟨hvalSixThree,h19Five,?_,?_,?_,?_⟩
    · rintro ⟨hj32',hm3,hmod⟩
      omega
    · rintro ⟨hj8',hm8',hmod⟩
      omega
    · rintro ⟨hm32',hj32'⟩
      omega
    ·
      have hx : 2*j+3=641+1024*u := by omega
      have hsum4 :
          (2*j+3+(2:Nat)^(2*m+2)*(j+3)-(j+3*m+5))%4=3 := by
        rw [hk,hx]
        omega
      have hnotAffine :
          ¬(4≤(2:Nat)^(2*m+2)*(j+3)-(j+3*m+5) ∧
            (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)%2=0 ∧
            (2*j+3+(2:Nat)^(2*m+2)*(j+3)-(j+3*m+5))%4=1) := by
        intro h
        rcases h with ⟨hk4,hk2,hgate⟩
        rw [hk,hx] at hgate
        omega
      have hnorm :
          BB6.Agent15.affineNormalize (2*j+3)
            ((2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)) =
            (2*j+3,(2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)) := by
        unfold BB6.Agent15.affineNormalize
        rw [dif_neg hnotAffine]
      rw [hnorm]
      intro hfour
      rw [hk] at hfour
      omega

/-- The second strict s3 image family is removed from the integrated
    Agent 3/11/19/29 high parameter predicate, without changing the
    exact low branch or the source-exact fixed-target root decision. -/
def highAllowedValSixFullS3 (j m : Nat) : Prop :=
  BB6.Agent3ValSix.highAllowedValSixFull j m ∧
  ¬(∃ u v, j=319+512*u ∧
    (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v ∧
    (u+v)%16=(15+4*u)%16)

theorem blank_halts_iff_joint_val_six_full_s3 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent3ValSix.lowAllowedValSixFull m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedValSixFullS3 j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent3ValSix.blank_halts_iff_joint_val_six_full]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff
          (2*j+3) k).mp hroot
      have hnot :
          ¬(∃ u v, j=319+512*u ∧ k=574+1024*v ∧
            (u+v)%16=(15+4*u)%16) := by
        rintro ⟨u,v,hj,hk,hsector⟩
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

theorem s3_image_family_removed_from_joint_full (j m u v : Nat)
    (hm7 : 7≤m)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v)
    (hsector : (u+v)%16=(15+4*u)%16) :
    ¬highAllowedValSixFullS3 j m := by
  intro h
  exact h.2 ⟨u,v,hj,hk,hsector⟩

#print axioms prior_joint_full_admits_s3_image_family
#print axioms blank_halts_iff_joint_val_six_full_s3
#print axioms s3_image_family_removed_from_joint_full

end BB6.Agent4SevenJointFull

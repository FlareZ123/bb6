import CSixSeventhSixAll
import CSixSeventhS2Pullback
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace BB6.Agent34S2Pullback

/-- The latest six-all high predicate with both S2 and complementary q-even
    high-stop cylinders removed. The low branch is unchanged. -/
def highAllowedAllS2Q (j m : Nat) : Prop :=
  BB6.Agent4SevenSixAll.highAllowedAllS3Six j m ∧
  ¬(j%512=319 ∧ (3*m+102921)%131072=(185*j)%131072) ∧
  ¬(j%512=319 ∧ (171*m+355585)%1048576=(49*j)%1048576)

/-- Exact original-source blank-halting iff after adding the two new
    all-time high-stop root exclusions to the latest six-all criterion. -/
private theorem high_stop_bound (j m : Nat) :
    j+3*m+5 ≤ (2:Nat)^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ (2:Nat)^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ (2:Nat)^(2*m+2) :=
    Nat.pow_pos (by decide)
  have hjle : j ≤ (2:Nat)^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

private theorem high_stop_identity (j m : Nat) :
    highK j m+(j+3*m+5)=(2:Nat)^(2*m+2)*(j+3) :=
  Nat.sub_add_cancel (high_stop_bound j m)

/-- The six-sector normalizer does not reject any high-stop target
    in the common j=319, m=42 (mod 512) base residue cylinder. -/
private theorem prior_six_forced_admits_base_residue (j m : Nat)
    (hj : j%512=319) (hm : m%512=42) :
    BB6.Agent11SixForced.sixForcedExcluded (2*j+3) (highK j m)=false := by
  have hm42 : 42≤m := by omega
  have hj16 : j%16=15 := by
    have hdiv : 16∣512 := by decide
    have hmod := Nat.mod_mod_of_dvd j hdiv
    rw [hj] at hmod
    omega
  have hj8 : j%8=7 := by
    have hdiv : 8∣512 := by decide
    have hmod := Nat.mod_mod_of_dvd j hdiv
    rw [hj] at hmod
    omega
  have hm8 : m%8=2 := by
    have hdiv : 8∣512 := by decide
    have hmod := Nat.mod_mod_of_dvd m hdiv
    rw [hm] at hmod
    omega
  have hpow8 : 8∣(2:Nat)^(2*m+2) := by
    have hp : (2:Nat)^3∣(2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^3=8 by decide] using hp
  have hprod8 : 8∣(2:Nat)^(2*m+2)*(j+3) := by
    obtain ⟨q,hq⟩ := hpow8
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hdiv8 : 8∣highK j m+(j+3*m+5) := by
    rw [high_stop_identity]
    exact hprod8
  have hmod8 := Nat.mod_eq_zero_of_dvd hdiv8
  have hx : (2*j+3)%2=1 := by omega
  have hx16 : (2*j+3)%16=1 := by omega
  have hsumBase8 : (j+3*m+5)%8=2 := by omega
  have hy8 : highK j m%8=6 := by omega
  have hy2 : highK j m%2=0 := by omega
  have hsum4 : (2*j+3+highK j m)%4=3 := by omega
  have hsum8 : (2*j+3+highK j m)%8=7 := by omega
  have hnotOdd :
      ¬BB6.Agent3.oddLowGate (2*j+3) (highK j m) := by
    intro h
    simp [BB6.Agent3.oddLowGate,hy2] at h
  have hnotSeven :
      ¬BB6.Agent3.evenSevenGate (2*j+3) (highK j m) := by
    intro h
    simp [BB6.Agent3.evenSevenGate,hx,hy2] at h
  have hnotAffine :
      ¬BB6.Agent3.evenAffineGate (2*j+3) (highK j m) := by
    intro h
    simp [BB6.Agent3.evenAffineGate,hsum4] at h
  have hnotSix :
      ¬BB6.Agent46.sixEvenRightGate (2*j+3) (highK j m) := by
    intro h
    simp [BB6.Agent46.sixEvenRightGate,hsum8] at h
  have hnotValSix :
      ¬BB6.Agent3ValSix.valSixGate (2*j+3) (highK j m) := by
    intro h
    simp [BB6.Agent3ValSix.valSixGate,hx16] at h
  have hnotEvenOdd :
      ¬BB6.Agent11SixForced.evenOddFourGate (2*j+3) (highK j m) := by
    intro h
    simp [BB6.Agent11SixForced.evenOddFourGate,hx,hy2] at h
  have hnorm :
      BB6.Agent11SixForced.sixForcedNormalize (2*j+3) (highK j m)=
        (2*j+3,highK j m) := by
    simp [BB6.Agent11SixForced.sixForcedNormalize,
      hnotOdd,hnotSeven,hnotAffine,hnotSix,hnotValSix,hnotEvenOdd]
  simp [BB6.Agent11SixForced.sixForcedExcluded,hnorm,hy2]

/-- Every high parameter in the base residue cylinder was admitted by
    the entire preceding C58/all-depth/late-fast/diagonal/m=0/six-sector
    high predicate. This makes subsequent subcylinder exclusions
    provably nonredundant, rather than merely syntactically narrower. -/
theorem prior_six_all_admits_base_residue (j m : Nat)
    (hj : j%512=319) (hm : m%512=42) :
    BB6.Agent11SixAll.highAllowed j m := by
  have hm7 : 7≤m := by omega
  have hlate :=
    BB6.Agent4SevenC58.prior_latefast_admits_base_residue j m hm7 hj hm
  have hm32 : m%32=10 := by omega
  have hjplus : (j+25)%32=24 := by omega
  have hdiag : BB6.Agent11DiagonalLate.highAllowed j m := by
    refine ⟨hlate,?_⟩
    rintro ⟨hm2,hjodd,hmod⟩
    omega
  have hmzero1 : ¬(m=0 ∧ j%128=71) := by omega
  have hmzero2 : ¬(m=0 ∧ j%2048=1159) := by omega
  have hdiagM0 : BB6.Agent11DiagonalM0.highAllowed j m :=
    ⟨hdiag,hmzero1⟩
  have hdeep : BB6.Agent11M0DeepFull.highAllowed j m :=
    ⟨hdiagM0,hmzero2⟩
  have hforced :
      BB6.Agent11SixForced.sixForcedExcluded (2*j+3)
        (2^(2*m+2)*(j+3)-(j+3*m+5))=false := by
    have heq : highK j m =
        (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5) := rfl
    simpa only [heq] using
      prior_six_forced_admits_base_residue j m hj hm
  change BB6.Agent11M0DeepFull.highAllowed j m ∧
    BB6.Agent11SixForced.sixForcedExcluded (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5))=false
  exact ⟨hdeep,hforced⟩

/-- Both new cylinders occupy the same mod-16384 lift, which is
    disjoint from the previously excluded S3 high-stop cylinder. -/
theorem prior_s3_admits_s2q_residue (j m : Nat)
    (hj : j%512=319) (hm512 : m%512=42)
    (hm16384 : m%16384=(7210+9728*(j/512))%16384) :
    BB6.Agent4SevenSixAll.highAllowedAllS3Six j m := by
  have hprior := prior_six_all_admits_base_residue j m hj hm512
  let u := j/512
  have hu : j=319+512*u := by dsimp [u]; omega
  have hmres : m%16384=(7210+9728*u)%16384 := by simpa [u] using hm16384
  have hs3 : (3*m+7*j+14025)%16384=5120 := by
    rw [hu]
    omega
  have hnotS3 :
      ¬(j%512=319 ∧ (3*m+7*j+14025)%16384=0) := by
    rintro ⟨_,hzero⟩
    omega
  exact ⟨hprior,hnotS3⟩

/-- The S2 cylinder is wholly admitted by the preceding S3-extended
    high predicate, so its removal is a strict strengthening. -/
theorem s2_cylinder_strict_nonredundancy (j m : Nat)
    (hj : j%512=319)
    (hm : m%131072=(72746+75264*(j/512))%131072) :
    BB6.Agent4SevenSixAll.highAllowedAllS3Six j m ∧
      ¬highAllowedAllS2Q j m := by
  have hdiv : 16384∣131072 := by decide
  have hm16384 :
      m%16384=(7210+9728*(j/512))%16384 := by
    calc
      m%16384=(m%131072)%16384 :=
        (Nat.mod_mod_of_dvd m hdiv).symm
      _=((72746+75264*(j/512))%131072)%16384 := by rw [hm]
      _=(72746+75264*(j/512))%16384 :=
        Nat.mod_mod_of_dvd _ hdiv
      _=(7210+9728*(j/512))%16384 := by omega
  have hdiv512 : 512∣16384 := by decide
  have hm512 : m%512=42 := by
    calc
      m%512=(m%16384)%512 :=
        (Nat.mod_mod_of_dvd m hdiv512).symm
      _=((7210+9728*(j/512))%16384)%512 := by rw [hm16384]
      _=(7210+9728*(j/512))%512 :=
        Nat.mod_mod_of_dvd _ hdiv512
      _=42 := by omega
  refine ⟨prior_s3_admits_s2q_residue j m hj hm512 hm16384,?_⟩
  intro h
  exact h.2.1 ((s2_parameter_pullback_iff j m).2 ⟨hj,hm⟩)

/-- The complementary q-even cylinder is also wholly admitted by the
    preceding S3-extended exact high predicate. -/
theorem q_even_cylinder_strict_nonredundancy (j m : Nat)
    (hj : j%512=319)
    (hm : m%1048576=(531498+337408*(j/512))%1048576) :
    BB6.Agent4SevenSixAll.highAllowedAllS3Six j m ∧
      ¬highAllowedAllS2Q j m := by
  have hdiv : 16384∣1048576 := by decide
  have hm16384 :
      m%16384=(7210+9728*(j/512))%16384 := by
    calc
      m%16384=(m%1048576)%16384 :=
        (Nat.mod_mod_of_dvd m hdiv).symm
      _=((531498+337408*(j/512))%1048576)%16384 := by rw [hm]
      _=(531498+337408*(j/512))%16384 :=
        Nat.mod_mod_of_dvd _ hdiv
      _=(7210+9728*(j/512))%16384 := by omega
  have hdiv512 : 512∣16384 := by decide
  have hm512 : m%512=42 := by
    calc
      m%512=(m%16384)%512 :=
        (Nat.mod_mod_of_dvd m hdiv512).symm
      _=((7210+9728*(j/512))%16384)%512 := by rw [hm16384]
      _=(7210+9728*(j/512))%512 :=
        Nat.mod_mod_of_dvd _ hdiv512
      _=42 := by omega
  refine ⟨prior_s3_admits_s2q_residue j m hj hm512 hm16384,?_⟩
  intro h
  exact h.2.2 ((q_even_parameter_pullback_iff j m).2 ⟨hj,hm⟩)

/-- Explicit nonempty infinite S2 progression, admitted by the old
    S3-extended criterion and removed by the new one. -/
theorem s2_progression_strict (u n : Nat) :
    BB6.Agent4SevenSixAll.highAllowedAllS3Six
      (319+512*u) (72746+75264*u+131072*n) ∧
    ¬highAllowedAllS2Q
      (319+512*u) (72746+75264*u+131072*n) := by
  have hj : (319+512*u)%512=319 := by omega
  have hu : (319+512*u)/512=u := by omega
  have hm : (72746+75264*u+131072*n)%131072=
      (72746+75264*((319+512*u)/512))%131072 := by
    rw [hu]
    omega
  exact s2_cylinder_strict_nonredundancy _ _ hj hm

/-- Explicit nonempty infinite q-even progression, admitted by the old
    S3-extended criterion and removed by the new one. -/
theorem q_even_progression_strict (u n : Nat) :
    BB6.Agent4SevenSixAll.highAllowedAllS3Six
      (319+512*u) (531498+337408*u+1048576*n) ∧
    ¬highAllowedAllS2Q
      (319+512*u) (531498+337408*u+1048576*n) := by
  have hj : (319+512*u)%512=319 := by omega
  have hu : (319+512*u)/512=u := by omega
  have hm : (531498+337408*u+1048576*n)%1048576=
      (531498+337408*((319+512*u)/512))%1048576 := by
    rw [hu]
    omega
  exact q_even_cylinder_strict_nonredundancy _ _ hj hm

#print axioms prior_s3_admits_s2q_residue
#print axioms s2_cylinder_strict_nonredundancy
#print axioms q_even_cylinder_strict_nonredundancy
#print axioms s2_progression_strict
#print axioms q_even_progression_strict

theorem blank_halts_iff_six_both_s2q :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision
          1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedAllS2Q j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision
          (2*j+3) (highK j m)=true) := by
  rw [BB6.Agent4SevenSixAll.blank_halts_iff_six_both_s3]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := highK j m
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff
          (2*j+3) k).mp hroot
      have hnotS2 :
          ¬(j%512=319 ∧
            (3*m+102921)%131072=(185*j)%131072) := by
        rintro ⟨hj,hcong⟩
        have hm := (s2_parameter_pullback_iff j m).1 ⟨hj,hcong⟩
        exact s2_high_parameter_not_CReach j m hj hm.2 hreach
      have hnotQ :
          ¬(j%512=319 ∧
            (171*m+355585)%1048576=(49*j)%1048576) := by
        rintro ⟨hj,hcong⟩
        have hm := (q_even_parameter_pullback_iff j m).1 ⟨hj,hcong⟩
        exact q_even_high_parameter_not_CReach j m hj hm.2 hreach
      exact Or.inr ⟨j,m,⟨hprior,hnotS2,hnotQ⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms highAllowedAllS2Q
#print axioms blank_halts_iff_six_both_s2q

end BB6.Agent34S2Pullback

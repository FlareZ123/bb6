import ValSixJointM1
import JointFiveSieve
import AffineFourGlobal
import Low124Stop
import High124Stop
import OddSevenSecondCylinder
import MixedRectangle27Zero
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

/-- Low parameters after merging Agent11's two image exclusions and
    Agent3's independent mod-128 blank-origin rectangle. -/
def lowAllowedValSixFull (m : Nat) : Prop :=
  BB6.Agent11Joint.lowAllowed m ∧
  ¬(128≤m ∧ m%128=0)

/-- Complete currently integrated high sieve:
    * Agent19/29's joint dyadic and modular restrictions;
    * Agent11's missing-image restrictions;
    * Agent19's sum-seven four-link family;
    * Agent29's four mod-128 families;
    * Agent3's three valuation-six families;
    * Agent3's low/high-124 stopping exclusions and the new branch of
      the 27/0 blank-origin rectangle not already covered by M512;
    * Agent19's second sum-seven inverse cylinder;
    * the general affine terminal-right-four exclusion. -/
def highAllowedValSixFull (j m : Nat) : Prop :=
  highAllowedValSixThree j m ∧
  BB6.Agent19Five.highAllowed j m ∧
  ¬(j%32=31 ∧ 3≤m ∧ (j+3*m)%128=127) ∧
  ¬(j%8=5 ∧ m%8=4 ∧ (9*j+39)%128=(3*m)%128) ∧
  ¬(m%32=21 ∧ j%32=28) ∧
  (BB6.Agent15.affineNormalize (2*j+3)
    (2^(2*m+2)*(j+3)-(j+3*m+5))).2 ≠ 4

private theorem low_bound_full (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_score_nonnegative_full (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- Agent19's second sum-seven inverse cylinder, pulled back through
    the exact high stopping equation. -/
private theorem high_second_slope_no_root
    (j m k : Nat)
    (hj : j%8=5) (hm : m%8=4)
    (hpair : (9*j+39)%128=(3*m)%128)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hr : BB6.Agent3.CReach (2*j+3) k) : False := by
  have hm4 : 4≤m := by omega
  have hpow128 : 128 ∣ (2:Nat)^(2*m+2) := by
    have hpow' : (2:Nat)^7 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa using hpow'
  have hprod128 : 128 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow128 with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hstopmod128 : (k+j+3*m+5)%128=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod128
  have hmod : (k+10*j+44)%128=0 := by omega
  have hpow16 : 16 ∣ (2:Nat)^(2*m+2) := by
    have hpow' : (2:Nat)^4 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa using hpow'
  have hprod16 : 16 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow16 with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hstopmod16 : (k+j+3*m+5)%16=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod16
  have hkmod16 : k%16=2 := by omega
  have hP : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hP1 : 1 ≤ 2^(2*m+2) := by omega
  have hjP : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hP1
  have h3P : 3*(4*m+4) ≤ 3*2^(2*m+2) :=
    Nat.mul_le_mul_left 3 hP
  have hmul : 2^(2*m+2)*(j+3)=
      2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    exact congrArg (fun z => 2^(2*m+2)*j+z)
      (Nat.mul_comm (2^(2*m+2)) 3)
  have hstopExpanded := hstop
  rw [hmul] at hstopExpanded
  have hk34 : 34≤k := by omega
  let u := (j-5)/8
  let v := (k-2)/16
  have hju : j=8*u+5 := by
    dsimp [u]
    omega
  have hkv : k=16*v+2 := by
    dsimp [v]
    omega
  have hv : 2≤v := by
    dsimp [v]
    omega
  have hres : (5*u+v)%8=2 := by
    rw [hju,hkv] at hmod
    omega
  have hreach : BB6.Agent3.CReach (16*u+13) (16*v+2) := by
    have hleft : 2*j+3=16*u+13 := by
      rw [hju]
      omega
    rw [hleft,hkv] at hr
    exact hr
  exact BB6.Agent19Second.blank_no_second_slope u v hv hres hreach

/-- High targets in the 27/0 rectangle are blank-unreachable after
    pulling the stopping equation back to the exact rectangle. -/
private theorem high_rectangle27_no_root
    (j m k : Nat)
    (hm : 2≤m) (hj : j%16=12)
    (hpair : (j+3*m+5)%32=0)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hr : BB6.Agent3.CReach (2*j+3) k) : False := by
  have hpow32 : 32 ∣ (2:Nat)^(2*m+2) := by
    have hpow' : (2:Nat)^5 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa using hpow'
  have hprod32 : 32 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow32 with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hstopmod : (k+j+3*m+5)%32=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod32
  have hkmod : k%32=0 := by omega
  have hxmod : (2*j+3)%32=27 := by omega
  have hP : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have h12P : 12 ≤ 2^(2*m+2) := by omega
  have h12j : 12*j ≤ 2^(2*m+2)*j :=
    Nat.mul_le_mul_right j h12P
  have h3P : 12*m+12 ≤ 3*2^(2*m+2) := by
    have h := Nat.mul_le_mul_left 3 hP
    omega
  have hmul : 2^(2*m+2)*(j+3)=
      2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    exact congrArg (fun z => 2^(2*m+2)*j+z)
      (Nat.mul_comm (2^(2*m+2)) 3)
  have hstopExpanded := hstop
  rw [hmul] at hstopExpanded
  have hsize : 64≤k := by omega
  exact BB6.Agent3.blank_no_rectangle_27_zero
    (2*j+3) k hxmod hkmod hsize hr

/-- Lossless original-source Machine C halting criterion after merging
    the currently established low/high restrictions from Agents 3, 11,
    19, and 29. The fixed-target root decision is exact; the remaining
    parameter existentials are unbounded and undecided. -/
theorem blank_halts_iff_joint_val_six_full :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedValSixFull m ∧
        valSixMixedRootDecision 1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedValSixFull j m ∧
        valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [blank_halts_iff_joint_val_six_fast]
  constructor
  · rintro (⟨m,hlow,hroot⟩ | ⟨j,m,hhigh,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (valSixMixedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (low_bound_full m)
        omega
      have hnon1 : m%4≠1 := by
        intro hm
        exact (BB6.Agent11Low.blank_no_low_m_one_mod_four
          m k hm hstop).2 hr
      have hnon2 : m%16≠7 := by
        intro hm
        exact (BB6.Agent11Low.blank_no_low_m_seven_mod16
          m k hm hstop).2 hr
      have hnon124 : ¬(128≤m ∧ m%128=0) := by
        rintro ⟨hm128,hmod⟩
        exact (BB6.Agent3.blank_no_low_m_zero_mod128
          m k hmod hm128 hstop) hr
      exact Or.inl ⟨m,⟨⟨hlow,hnon1,hnon2⟩,hnon124⟩,hroot⟩
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_score_nonnegative_full j m)
        omega
      have hbase : BB6.Agent19Joint.highAllowed j m := hhigh.1.1.1
      have hnon1 : (j+m)%4≠0 := by
        intro hjm
        exact (BB6.Agent11High.blank_no_high_jplusm_zero_modfour
          j m k hjm hstop).2 hr
      have hnon2 :
          ¬(2≤m ∧ (j+m)%16=6 ∧ m%4≠1) := by
        rintro ⟨hm,hjm,hm4⟩
        exact (BB6.Agent11High.blank_no_high_jplusm_six_mod16
          j m k hm hjm hm4 hstop) hr
      have h11 : BB6.Agent11Joint.highAllowed j m := by
        unfold BB6.Agent11Joint.highAllowed
        exact ⟨hbase,hnon1,hnon2⟩
      have hfourlink :
          ¬(m%16=10 ∧ (j+3*m+19)%64=0) := by
        rintro ⟨hm,hpair⟩
        exact BB6.Agent19Four.blank_no_high_fourlink
          j m k hm hpair hstop hr
      have h19 : BB6.Agent19Five.highAllowed j m := by
        unfold BB6.Agent19Five.highAllowed
        exact ⟨h11,hfourlink⟩
      have hnon124 :
          ¬(j%32=31 ∧ 3≤m ∧ (j+3*m)%128=127) := by
        rintro ⟨hj31,hm3,hpair⟩
        exact (BB6.Agent3.blank_no_high_124
          j m k hj31 hm3 hpair hstop) hr
      have hnonSecond :
          ¬(j%8=5 ∧ m%8=4 ∧ (9*j+39)%128=(3*m)%128) := by
        rintro ⟨hj5,hm4,hpair⟩
        exact high_second_slope_no_root j m k hj5 hm4 hpair hstop hr
      have hnon27 : ¬(m%32=21 ∧ j%32=28) := by
        rintro ⟨hm21,hj28⟩
        have hm2 : 2≤m := by omega
        have hj16 : j%16=12 := by omega
        have hpair : (j+3*m+5)%32=0 := by omega
        exact high_rectangle27_no_root j m k hm2 hj16 hpair hstop hr
      have hr15 : BB6.Agent15.CReach (2*j+3) k := hr
      have hright4 :
          (BB6.Agent15.affineNormalize (2*j+3) k).2≠4 := by
        intro hfour
        have hclass :=
          (BB6.Agent29Bottom.blank_affine_four_odd_iff
            (2*j+3) k (by omega) hfour).mp hr15
        have hk7 := BB6.Agent15.second_halt_k_ge_seven j m k hstop
        omega
      exact Or.inr
        ⟨j,m,⟨hhigh,h19,hnon124,hnonSecond,hnon27,hright4⟩,hroot⟩
  · rintro (⟨m,hallow,hroot⟩ |
      ⟨j,m,⟨hhigh,_,_,_,_,_⟩,hroot⟩)
    · exact Or.inl ⟨m,hallow.1.1,hroot⟩
    · exact Or.inr ⟨j,m,hhigh,hroot⟩

/-- The explicit m=1 tower is admitted by both prior high sieves,
    including Agent11's extra restrictions and Agent19's four-link
    family, before the affine terminal-right-four exclusion is applied. -/
theorem second_one_family_previous_sieves (r : Nat) :
    highAllowedValSixThree (BB6.Agent29Depth.secondOneJ r) 1 ∧
    BB6.Agent19Five.highAllowed (BB6.Agent29Depth.secondOneJ r) 1 := by
  have h3 := second_one_family_previously_allowed r
  have hbase : BB6.Agent19Joint.highAllowed
      (BB6.Agent29Depth.secondOneJ r) 1 := h3.1.1.1
  have hmod := BB6.Agent29Depth.secondOneJ_mod32 r
  have h11 : BB6.Agent11Joint.highAllowed
      (BB6.Agent29Depth.secondOneJ r) 1 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨hbase, by omega, by omega⟩
  have h19 : BB6.Agent19Five.highAllowed
      (BB6.Agent29Depth.secondOneJ r) 1 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11, by omega⟩
  exact ⟨h3,h19⟩

/-- The m=1 tower is removed by the general affine terminal-right-four
    predicate. -/
theorem second_one_family_removed_by_affine_four (r : Nat) :
    ¬ highAllowedValSixFull (BB6.Agent29Depth.secondOneJ r) 1 := by
  intro h
  have hstop := BB6.Agent29Depth.second_one_family_stopping r
  have hpow : (2:Nat)^(2*1+2)=16 := by decide
  have hk :
      (2:Nat)^(2*1+2)*(BB6.Agent29Depth.secondOneJ r+3) -
        (BB6.Agent29Depth.secondOneJ r+3*1+5) =
      15*BB6.Agent29Depth.secondOneJ r+40 := by
    rw [hpow] at hstop ⊢
    omega
  have hfour :
      (BB6.Agent15.affineNormalize
        (2*BB6.Agent29Depth.secondOneJ r+3)
        (2^(2*1+2)*(BB6.Agent29Depth.secondOneJ r+3) -
          (BB6.Agent29Depth.secondOneJ r+3*1+5))).2=4 := by
    simpa [hk] using
      BB6.Agent29Depth.second_one_family_normalizes_four r
  rcases h with ⟨_,_,_,_,_,hright⟩
  exact hright hfour

/-- The mod-128 low family is admitted by the older Agent3/11 low
    sieve, so its removal is a genuinely additional restriction. -/
theorem low_124_family_previous_sieve (m : Nat)
    (hm : 128≤m) (hmod : m%128=0) :
    BB6.Agent11Joint.lowAllowed m := by
  unfold BB6.Agent11Joint.lowAllowed BB6.Agent3.jointLowAllowed
  omega

/-- The high-124 family survives all prior Agent3/11/19/29
    high restrictions, so the new source rectangle removes a genuinely
    additional infinite family. -/
theorem high_124_family_previous_sieves (j m : Nat)
    (hj : j%32=31) (hm : 3≤m)
    (hpair : (j+3*m)%128=127) :
    highAllowedValSixThree j m ∧
      BB6.Agent19Five.highAllowed j m := by
  have hm32 : m%32=0 := by omega
  have hjoint : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    constructor
    · unfold BB6.Agent3.jointHighAllowed
      refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
    · omega
  have hdy : ∀ n, ¬
      (n+4≤2*m+2 ∧ (j+3*m+3)%2^(n+4)=2^(n+2) ∧
        (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hres⟩
    have hx : (2*j+3)%8=1 := by omega
    by_cases hn : n%2=0
    · simp [hn] at hres
      omega
    · simp [hn] at hres
      omega
  have hbase : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    have hodd1 :
        ¬(2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) := by omega
    have hodd2 :
        ¬(2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) := by omega
    have hodd3 :
        ¬(3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) := by omega
    have hodd4 :
        ¬(3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0) := by omega
    exact ⟨hjoint,hdy,hodd1,hodd2,hodd3,hodd4⟩
  have hplus : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨hbase,by omega,by omega,by omega,by omega⟩
  have hval : highAllowedValSixThree j m := by
    unfold highAllowedValSixThree highAllowedValSix
    exact ⟨⟨hplus,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨hbase,by omega,by omega⟩
  have h19 : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  exact ⟨hval,h19⟩

/-- The explicit infinite high-124 family is admitted by the previous
    high sieve before the new 124 exclusion. -/
theorem high124_infinite_family_previous_sieves (r : Nat) :
    highAllowedValSixThree 31 (32+128*r) ∧
      BB6.Agent19Five.highAllowed 31 (32+128*r) := by
  exact high_124_family_previous_sieves 31 (32+128*r)
    (by omega) (by omega) (by omega)

/-- Concrete M512-admitted member of the new 27/0 branch survives
    the previous exact Agent3/11/19/29 high sieve. -/
theorem rectangle27_sample_previous_sieves :
    highAllowedValSixThree 28 85 ∧
      BB6.Agent19Five.highAllowed 28 85 := by
  have hjoint : BB6.Agent3.jointHighRectAllowed 28 85 := by
    unfold BB6.Agent3.jointHighRectAllowed
    constructor
    · unfold BB6.Agent3.jointHighAllowed
      refine ⟨?_,?_,?_,?_,?_⟩ <;> decide
    · decide
  have hdy : ∀ n, ¬
      (n+4≤2*85+2 ∧ (28+3*85+3)%2^(n+4)=2^(n+2) ∧
        (2*28+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,hres,hx⟩
    by_cases heven : n%2=0
    · simp [heven] at hx
    · have hnodd : n%2=1 := by omega
      have hnCases : n=1 ∨ 3≤n := by omega
      rcases hnCases with rfl | hn3
      · omega
      · have hdiv : 32 ∣ (2:Nat)^(n+4) := by
          have hpow : (2:Nat)^5 ∣ (2:Nat)^(n+4) :=
            Nat.pow_dvd_pow 2 (by omega)
          simpa using hpow
        have hleft :
            (286%(2:Nat)^(n+4))%32=286%32 :=
          Nat.mod_mod_of_dvd 286 hdiv
        have hdivR : 32 ∣ (2:Nat)^(n+2) := by
          have hpow : (2:Nat)^5 ∣ (2:Nat)^(n+2) :=
            Nat.pow_dvd_pow 2 (by omega)
          simpa using hpow
        have hright : (2:Nat)^(n+2)%32=0 :=
          Nat.mod_eq_zero_of_dvd hdivR
        have hcong := congrArg (fun z : Nat => z%32) hres
        rw [hleft,hright] at hcong
        omega
  have hbase : BB6.Agent19Joint.highAllowed 28 85 := by
    unfold BB6.Agent19Joint.highAllowed
    have hodd1 :
        ¬(2≤85 ∧ 28%8=7 ∧ (28+3*85+15)%64=0) := by decide
    have hodd2 :
        ¬(2≤85 ∧ 28%8=3 ∧ (28+3*85+47)%64=0) := by decide
    have hodd3 :
        ¬(3≤85 ∧ 28%8=5 ∧ (28+3*85+27)%128=0) := by decide
    have hodd4 :
        ¬(3≤85 ∧ 28%8=1 ∧ (28+3*85+91)%128=0) := by decide
    exact ⟨hjoint,hdy,hodd1,hodd2,hodd3,hodd4⟩
  have hplus : BB6.Agent29Joint.highAllowedPlus 28 85 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨hbase,by decide,by decide,by decide,by decide⟩
  have hval : highAllowedValSixThree 28 85 := by
    unfold highAllowedValSixThree highAllowedValSix
    exact ⟨⟨hplus,by decide,by decide⟩,by decide⟩
  have h11 : BB6.Agent11Joint.highAllowed 28 85 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨hbase,by decide,by decide⟩
  have h19 : BB6.Agent19Five.highAllowed 28 85 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by decide⟩
  exact ⟨hval,h19⟩

/-- The second sum-seven cylinder also survives the previous
    Agent19/29/3 high sieve; it is a genuinely new high restriction. -/
theorem second_slope_family_previous_sieves (j m : Nat)
    (hj : j%8=5) (hm : m%8=4)
    (hpair : (9*j+39)%128=(3*m)%128) :
    highAllowedValSixThree j m ∧
      BB6.Agent19Five.highAllowed j m := by
  have hjoint : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    constructor
    · unfold BB6.Agent3.jointHighAllowed
      refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
    · omega
  have hdy : ∀ n, ¬
      (n+4≤2*m+2 ∧ (j+3*m+3)%2^(n+4)=2^(n+2) ∧
        (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hres⟩
    have hx : (2*j+3)%8=5 := by omega
    by_cases hn : n%2=0
    · simp [hn] at hres
      omega
    · simp [hn] at hres
      omega
  have hbase : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    have hodd1 :
        ¬(2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) := by omega
    have hodd2 :
        ¬(2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) := by omega
    have hodd3 :
        ¬(3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) := by
      rintro ⟨_,_,hzero⟩
      have hmod8 : (j+3*m+27)%8=4 := by omega
      omega
    have hodd4 :
        ¬(3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0) := by omega
    exact ⟨hjoint,hdy,hodd1,hodd2,hodd3,hodd4⟩
  have hplus : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    refine ⟨hbase,?_,?_,?_,?_⟩
    · rintro ⟨_,_,heq⟩
      have h16 : j%16=15 := by omega
      omega
    · omega
    · omega
    · omega
  have hval : highAllowedValSixThree j m := by
    unfold highAllowedValSixThree highAllowedValSix
    exact ⟨⟨hplus,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨hbase,by omega,by omega⟩
  have h19 : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  exact ⟨hval,h19⟩

/-- Infinite low-124 parameter family removed by the merged low sieve. -/
theorem low124_infinite_family_removed (r : Nat) :
    ¬ lowAllowedValSixFull (128*(r+1)) := by
  intro h
  rcases h with ⟨_,hfilter⟩
  exact hfilter ⟨by omega,by omega⟩

/-- Infinite high-124 parameter family removed by the merged high sieve. -/
theorem high124_infinite_family_removed (r : Nat) :
    ¬ highAllowedValSixFull 31 (32+128*r) := by
  intro h
  rcases h with ⟨_,_,hfilter,_,_,_⟩
  exact hfilter ⟨by omega,by omega,by omega⟩

/-- Infinite second-slope family removed by the new Agent19 cylinder
    pullback; the prior-sieve theorem below shows this family survived
    the previous Agent3/11/19/29 restrictions. -/
theorem second_slope_infinite_family_removed (r : Nat) :
    ¬ highAllowedValSixFull 5 (28+128*r) := by
  intro h
  rcases h with ⟨_,_,_,hfilter,_,_⟩
  exact hfilter ⟨by omega,by omega,by omega⟩

/-- Infinite 27/0 rectangle family in the new M512-admitted branch. -/
theorem rectangle27_infinite_family_removed (r : Nat) :
    ¬ highAllowedValSixFull 28 (21+32*r) := by
  intro h
  rcases h with ⟨_,_,_,_,hfilter,_⟩
  exact hfilter ⟨by omega,by omega⟩

/-- The explicit infinite second-slope family is admitted by the
    previous high sieve before the new cylinder exclusion. -/
theorem second_slope_infinite_family_previous_sieves (r : Nat) :
    highAllowedValSixThree 5 (28+128*r) ∧
      BB6.Agent19Five.highAllowed 5 (28+128*r) := by
  exact second_slope_family_previous_sieves 5 (28+128*r)
    (by omega) (by omega) (by omega)

#print axioms blank_halts_iff_joint_val_six_full
#print axioms second_one_family_previous_sieves
#print axioms second_one_family_removed_by_affine_four
#print axioms low_124_family_previous_sieve
#print axioms second_slope_family_previous_sieves
#print axioms low124_infinite_family_removed
#print axioms high124_infinite_family_removed
#print axioms high_124_family_previous_sieves
#print axioms high124_infinite_family_previous_sieves
#print axioms second_slope_infinite_family_removed
#print axioms rectangle27_infinite_family_removed
#print axioms rectangle27_sample_previous_sieves
#print axioms second_slope_infinite_family_previous_sieves

end BB6.Agent3ValSix

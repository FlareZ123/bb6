import EvenOddLowStopEvenReachIff
import EvenOddLowStopSecondPowerGap
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowSecondFan
open BB6.Agent46

private theorem linear_le_power (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

private theorem second_parent_facts (s u : Nat)
    (hu : u+12*s+1=2^(2048*s+129)) :
    5 < 173*u+24 ∧
    6 ≤ (339*u+47)/2 ∧
    ((339*u+47)/2)%2=0 ∧
    ((173*u+24)+((339*u+47)/2))%2=1 := by
  have hpow4 : (2:Nat)^2 ∣ 2^(2048*s+129) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hdiv4 : 4 ∣ u+12*s+1 := by
    rw [hu]
    simpa only [show (2:Nat)^2=4 by decide] using hpow4
  have hmod4 : (u+12*s+1)%4=0 :=
    Nat.mod_eq_zero_of_dvd hdiv4
  have hu3 : u%4=3 := by omega
  have hnum4 : (339*u+47)%4=0 := by omega
  have hyEven : ((339*u+47)/2)%2=0 := by
    have hnumDiv : 4 ∣ 339*u+47 :=
      Nat.dvd_of_mod_eq_zero hnum4
    rcases hnumDiv with ⟨q,hq⟩
    have hquot : (339*u+47)/2=2*q := by omega
    rw [hquot]
    omega
  have hlin : 2048*s+130 ≤ 2^(2048*s+129) :=
    linear_le_power _
  have huLarge : 129 ≤ u := by omega
  have hyLarge : 6 ≤ (339*u+47)/2 := by omega
  have hxLarge : 5 < 173*u+24 := by omega
  have hsumOdd :
      ((173*u+24)+((339*u+47)/2))%2=1 := by omega
  exact ⟨hxLarge,hyLarge,hyEven,hsumOdd⟩

/-- The only possible non-direct parents of the second-generation
    target P=(173u+24,(339u+47)/2) are odd-depth, odd-left high bounces.
    The direct affine parent is always present. The exceptional a=1
    power-of-two branch is excluded by the source-certified second-level
    strict mass gap. This is an exact original-source iff, with no depth
    or parameter cutoff. -/
def secondHighParentCondition (s u n a k : Nat) : Prop :=
  n%2=1 ∧ a%2=1 ∧ 3≤a ∧ a<2*k ∧
  (173*u+25+(339*u+47)/2 = 2^(n+1)*(a+3)) ∧
  (2*k+a+7+3*n = (173*u+24)+2*((339*u+47)/2))

theorem second_parent_source_parent_iff
    (s u a k : Nat)
    (hu : u+12*s+1=2^(2048*s+129)) :
    secNext (a,k)=some (173*u+24,(339*u+47)/2) ↔
      (a=173*u+24+((339*u+47)/2)-2 ∧
       k=(((339*u+47)/2)-2)/2) ∨
      secondHighParentCondition s u 0 a k ∨
      (∃ n : Nat, secondHighParentCondition s u n a k) := by
  have ⟨hxLarge,hyLarge,hyEven,hxyOdd⟩ :=
    second_parent_facts s u hu
  have hy : 5 ≤ (339*u+47)/2 := by omega
  have hS :
      173*u+25+(339*u+47)/2 =
        (173*u+24)+((339*u+47)/2)+1 := by omega
  have hSnp :=
    BB6.Agent13LowSecondPowerGap.second_parent_mass_not_power_two s u hu
  constructor
  · intro hedge
    have hp := (complete_section_inverse a k (173*u+24)
      ((339*u+47)/2) hy).mp hedge
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,hk0] at hp
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,ha0,hk0,hk1] at hp
          omega
        · simp only [sectionPreimageCriterion,if_pos ha0,
              if_neg hk0,if_neg hk1] at hp
          rcases hp with ⟨n,hpow,_⟩
          have heven : ((173*u+24)+((339*u+47)/2))%2=0 := by
            rw [hpow]
            simp [Nat.mul_mod]
          omega
    · by_cases ha1 : a=1
      · by_cases hk0 : k=0
        · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hp
        · by_cases hk1 : k=1
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at hp
          · by_cases hk2 : k=2
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2] at hp
              omega
            · by_cases hk3 : k=3
              · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at hp
                omega
              · simp only [sectionPreimageCriterion,if_neg ha0,
                    if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,
                    if_neg hk3] at hp
                rcases hp with ⟨n,hpow,_⟩
                have hpowMass :
                    173*u+25+(339*u+47)/2=2^(n+4) := by
                  calc
                    173*u+25+(339*u+47)/2 =
                        (173*u+24)+((339*u+47)/2)+1 := hS
                    _ = 2^n*16 := hpow
                    _ = 2^(n+4) := by
                      rw [Nat.pow_add]
                      norm_num
                exact (hSnp (n+4) hpowMass).elim
      · by_cases hk0 : k=0
        · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hp
        · by_cases hlow : 2*k≤a
          · simp only [sectionPreimageCriterion,if_neg ha0,
                if_neg ha1,if_neg hk0,if_pos hlow] at hp
            rcases hp with ⟨hX,hY⟩
            left
            constructor <;> omega
          · by_cases hae : a%2=0
            · simp only [sectionPreimageCriterion,if_neg ha0,
                  if_neg ha1,if_neg hk0,if_neg hlow,if_pos hae] at hp
              rcases hp with ⟨n,hpow,_⟩
              have heven : ((173*u+24)+((339*u+47)/2))%2=0 := by
                rw [hpow]
                simp [Nat.mul_mod]
              omega
            · simp only [sectionPreimageCriterion,if_neg ha0,
                  if_neg ha1,if_neg hk0,if_neg hlow,if_neg hae] at hp
              rcases hp with ⟨n,hpow,hcost⟩
              have haodd : a%2=1 := by omega
              have hnodd : n%2=1 := by omega
              have hfactor : 2*(a-1)+8=2*(a+3) := by omega
              have hmass :
                  173*u+25+(339*u+47)/2 =
                    2^(n+1)*(a+3) := by
                calc
                  173*u+25+(339*u+47)/2 =
                      (173*u+24)+((339*u+47)/2)+1 := hS
                  _ = 2^n*(2*(a-1)+8) := hpow
                  _ = 2^n*(2*(a+3)) := by rw [hfactor]
                  _ = 2^(n+1)*(a+3) := by
                    rw [Nat.pow_succ]
                    ac_rfl
              have hcost' :
                  2*k+a+7+3*n =
                    (173*u+24)+2*((339*u+47)/2) := by omega
              right
              right
              exact ⟨n,hnodd,haodd,by omega,by omega,hmass,hcost'⟩
  · rintro (⟨ha,hk⟩ | hzero | ⟨n,hcond⟩)
    · subst a
      subst k
      have ha0 : 173*u+24+((339*u+47)/2)-2 ≠ 0 := by omega
      have ha1 : 173*u+24+((339*u+47)/2)-2 ≠ 1 := by omega
      have hk0 : ((339*u+47)/2-2)/2 ≠ 0 := by omega
      have hlow :
          2*(((339*u+47)/2-2)/2) ≤
            173*u+24+((339*u+47)/2)-2 := by omega
      have hp : sectionPreimageCriterion
          (173*u+24+((339*u+47)/2)-2)
          (((339*u+47)/2-2)/2)
          (173*u+24) ((339*u+47)/2) := by
        simp only [sectionPreimageCriterion,if_neg ha0,
          if_neg ha1,if_neg hk0,if_pos hlow]
        omega
      exact (complete_section_inverse _ _ _ _ hy).mpr hp
    · rcases hzero with ⟨hn,haodd,ha3,hregion,hmass,hcost⟩
      have ha0 : a≠0 := by omega
      have ha1 : a≠1 := by omega
      have hk0 : k≠0 := by omega
      have hhigh : ¬ 2*k≤a := by omega
      have hae : ¬ a%2=0 := by omega
      have hfactor : 2*(a-1)+8=2*(a+3) := by omega
      have hpow :
          (173*u+24)+((339*u+47)/2)+1 =
            2^0*(2*(a-1)+8) := by
        rw [hmass]
        simp [hfactor]
      have hcost' :
          (2*k-a+3)+(2*(a-1)+8)+3*0 =
            (173*u+24)+2*((339*u+47)/2)+2 := by omega
      have hp : sectionPreimageCriterion a k
          (173*u+24) ((339*u+47)/2) := by
        simp only [sectionPreimageCriterion,if_neg ha0,
          if_neg ha1,if_neg hk0,if_neg hhigh,if_neg hae]
        exact ⟨0,hpow,hcost'⟩
      exact (complete_section_inverse _ _ _ _ hy).mpr hp
    · rcases hcond with ⟨hn,haodd,ha3,hregion,hmass,hcost⟩
      have ha0 : a≠0 := by omega
      have ha1 : a≠1 := by omega
      have hk0 : k≠0 := by omega
      have hhigh : ¬ 2*k≤a := by omega
      have hae : ¬ a%2=0 := by omega
      have hfactor : 2*(a-1)+8=2*(a+3) := by omega
      have hpow :
          (173*u+24)+((339*u+47)/2)+1 =
            2^n*(2*(a-1)+8) := by
        rw [hmass]
        rw [Nat.pow_succ]
        rw [hfactor]
        ac_rfl
      have hcost' :
          (2*k-a+3)+(2*(a-1)+8)+3*n =
            (173*u+24)+2*((339*u+47)/2)+2 := by omega
      have hp : sectionPreimageCriterion a k
          (173*u+24) ((339*u+47)/2) := by
        simp only [sectionPreimageCriterion,if_neg ha0,
          if_neg ha1,if_neg hk0,if_neg hhigh,if_neg hae]
        exact ⟨n,hpow,hcost'⟩
      exact (complete_section_inverse _ _ _ _ hy).mpr hp

#print axioms second_parent_source_parent_iff

/-- Every high-bounce parent in the exact second-generation fan has
    odd depth bounded by the 2-adic valuation of 3*(685s+49).
    The divisor equivalence is exact for every exponent; no finite
    parameter or depth cutoff is used. -/
theorem second_high_parent_depth_divides
    (s u n a k : Nat)
    (hu : u+12*s+1=2^(2048*s+129))
    (hcond : secondHighParentCondition s u n a k) :
    2^n ∣ 3*(685*s+49) := by
  rcases hcond with ⟨hn,haodd,ha3,hregion,hmass,hcost⟩
  have hdiv :
      2^(n+2) ∣ 2*(173*u+25+(339*u+47)/2) := by
    refine ⟨a+3,?_⟩
    calc
      2*(173*u+25+(339*u+47)/2) =
          2*(2^(n+1)*(a+3)) := by rw [hmass]
      _ = 2^(n+2)*(a+3) := by
        rw [Nat.pow_succ]
        ac_rfl
  exact (BB6.Agent13LowSecondDyadic.second_low_parent_mass_dyadic_iff
    s u n hu).mp hdiv

/-- Exact blank-root reachability decomposition for the second-generation
    target P. A root hit occurs iff the direct affine parent is hit, or
    one of the source-exact odd-depth high-bounce parents is hit. -/
theorem second_parent_reach_iff
    (s u : Nat)
    (hu : u+12*s+1=2^(2048*s+129)) :
    BB6.Agent3.CReach (173*u+24) ((339*u+47)/2) ↔
      BB6.Agent3.CReach
        (173*u+24+((339*u+47)/2)-2)
        (((339*u+47)/2-2)/2) ∨
      (∃ n a k, secondHighParentCondition s u n a k ∧
        BB6.Agent3.CReach a k) := by
  have ⟨hxLarge,hyLarge,hyEven,hxyOdd⟩ :=
    second_parent_facts s u hu
  constructor
  · intro hr
    obtain ⟨a,k,hpre,hedge⟩ :=
      BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
        (173*u+24) ((339*u+47)/2) hxLarge hr
    rcases (second_parent_source_parent_iff s u a k hu).mp hedge with
      hdir | hzero | ⟨n,hcond⟩
    · rcases hdir with ⟨ha,hk⟩
      left
      rw [ha,hk] at hpre
      exact hpre
    · exact Or.inr ⟨0,a,k,hzero,hpre⟩
    · exact Or.inr ⟨n,a,k,hcond,hpre⟩
  · rintro (hdir | ⟨n,a,k,hcond,hrparent⟩)
    · rcases hdir with ⟨time,ht⟩
      have hedge : secNext
          (173*u+24+((339*u+47)/2)-2,(((339*u+47)/2)-2)/2) =
            some (173*u+24,(339*u+47)/2) :=
        (second_parent_source_parent_iff s u
          (173*u+24+((339*u+47)/2)-2)
          ((((339*u+47)/2)-2)/2) hu).mpr
            (Or.inl ⟨rfl,rfl⟩)
      exact ⟨time+1,by simpa [BB6.Agent8Section.run,ht] using hedge⟩
    · rcases hrparent with ⟨time,ht⟩
      have hedge : secNext (a,k)=some (173*u+24,(339*u+47)/2) :=
        (second_parent_source_parent_iff s u a k hu).mpr
          (Or.inr (Or.inr ⟨n,hcond⟩))
      exact ⟨time+1,by simpa [BB6.Agent8Section.run,ht] using hedge⟩

#print axioms second_parent_reach_iff

/-- On the residual sum-seven subfamily s=4r+3 with odd r, every
    high-bounce parent has depth exactly one. This follows from the
    exact second-generation dyadic divisor, not a bounded scan. -/
theorem second_high_parent_depth_one_of_odd_r
    (r u n a k : Nat)
    (hu : u+12*(4*r+3)+1=2^(2048*(4*r+3)+129))
    (hr : r%2=1)
    (hcond : secondHighParentCondition (4*r+3) u n a k) :
    n=1 := by
  have hdvd := second_high_parent_depth_divides (4*r+3) u n a k hu hcond
  have hidentity :
      3*(685*(4*r+3)+49)=12*(685*r+526) := by omega
  have hodd : (685*r+526)%2=1 := by omega
  have hnlt : n<3 := by
    by_contra hnlt
    have hnge : 3≤n := by omega
    have hpow8 : 8∣2^n := by
      have hh : (2:Nat)^3∣2^n := Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^3=8 by decide] using hh
    have hdiv8 : 8∣3*(685*(4*r+3)+49) :=
      Nat.dvd_trans hpow8 hdvd
    have hmod8 :
        (3*(685*(4*r+3)+49))%8=0 :=
      Nat.mod_eq_zero_of_dvd hdiv8
    rw [hidentity] at hmod8
    omega
  omega

/-- For z=8r+6 with odd r, the original low-stop target is reduced
    exactly to two candidate blank-root ancestors: the direct parent
    and the unique possible high-bounce parent at depth one. -/
theorem low_ray_z14_second_fan_reach_iff
    (r u : Nat)
    (hu : u+12*(4*r+3)+1=2^(2048*(4*r+3)+129))
    (hr : r%2=1) :
    BB6.Agent3.CReach (180*u+28) (166*u+25) ↔
      BB6.Agent3.CReach
        (173*u+24+((339*u+47)/2)-2)
        (((339*u+47)/2-2)/2) ∨
      (∃ a k, secondHighParentCondition (4*r+3) u 1 a k ∧
        BB6.Agent3.CReach a k) := by
  have hfirstExp : 1024*(2*(4*r+3))+129 =
      2048*(4*r+3)+129 := by omega
  have hu' : u+6*(2*(4*r+3))+1 =
      2^(1024*(2*(4*r+3))+129) := by
    rw [hfirstExp]
    exact hu
  have hfirst :=
    BB6.Agent13LowEvenIff.even_low_ray_reach_iff_unique_parent
      (2*(4*r+3)) u hu' (by omega)
  have hsecond :=
    second_parent_reach_iff (4*r+3) u hu
  constructor
  · intro hrRoot
    have hP := hfirst.mp hrRoot
    rcases hsecond.mp hP with hdir | ⟨n,a,k,hcond,hreach⟩
    · exact Or.inl hdir
    · have hn1 :=
        second_high_parent_depth_one_of_odd_r r u n a k hu hr hcond
      subst n
      exact Or.inr ⟨a,k,hcond,hreach⟩
  · intro hparents
    apply hfirst.mpr
    apply hsecond.mpr
    exact hparents

#print axioms low_ray_z14_second_fan_reach_iff
end BB6.Agent13LowSecondFan

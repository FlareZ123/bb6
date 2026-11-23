import FullSectionInverse
import Agent38SectionParity
import EvenRightUnique
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent21Low1091
open BB6.Agent46

/-- Genuine blank-origin reachability for the unchanged Machine C section. -/
def CReach (a k : Nat) : Prop :=
  ∃ time : Nat,
    BB6.Agent8Section.run secNext time (some (5,1)) = some (a,k)

/-- Every non-seed blank-reachable state has a genuine immediate source parent. -/
private theorem cReach_parent_of_right5 (x y : Nat)
    (hy : 5≤y) (hr : CReach x y) :
    ∃ a k, CReach a k ∧ secNext (a,k)=some (x,y) := by
  have hneq : (x,y) ≠ (5,1) := by
    intro h
    cases Prod.mk.inj h
    omega
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero =>
      have hpair : (5,1)=(x,y) := by
        simpa [BB6.Agent8Section.run] using ht
      exact False.elim (hneq hpair.symm)
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          refine ⟨a,k,⟨n,hp⟩,?_⟩
          simpa [BB6.Agent8Section.run,hp] using ht

/-- A source-parent classification transports blank reachability to its
    uniquely determined predecessor. -/
private theorem cReach_of_unique_parent (x y a k : Nat)
    (hy : 5≤y)
    (huniq : ∀ b c, secNext (b,c)=some (x,y) → b=a ∧ c=k)
    (hr : CReach x y) : CReach a k := by
  obtain ⟨b,c,hrb,hedge⟩ := cReach_parent_of_right5 x y hy hr
  obtain ⟨rfl,rfl⟩ := huniq b c hedge
  exact hrb

/-- Odd/odd outputs with sum 4 modulo 8 have only their depth-zero
    even-left bounce predecessor. This is derived from the complete
    unbounded-depth original-source inverse predicate. -/
private theorem odd_odd_sum4_parent (a k x y : Nat)
    (hx0 : x≠0) (hx2 : x≠2)
    (hy : 5≤y) (hxo : x%2=1) (hyo : y%2=1)
    (hs : (x+y)%8=4)
    (hedge : secNext (a,k)=some (x,y)) :
    a=(x+y)/2-2 ∧ k=(x+2*y-a-7)/2 := by
  have hp := (complete_section_inverse a k x y hy).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageCriterion,ha0,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageCriterion,if_pos ha0,if_neg hk0,if_neg hk1] at hp
        rcases hp with ⟨n,hpow,_⟩
        have hdiv : (x+y)%8=0 := by
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
            · simp only [sectionPreimageCriterion,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
              rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hodd : (x+y+1)%2=1 := by omega
                have heven : (2^n*16)%2=0 := by simp
                rw [hpow] at hodd
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hp
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hlow] at hp
          rcases hp with ⟨_,hyEq⟩
          have hyEven : y%2=0 := by rw [hyEq]; omega
          omega
        · by_cases haeven : a%2=0
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos haeven] at hp
            rcases hp with ⟨n,hpow,hcost⟩
            cases n with
            | zero =>
                simp at hpow hcost
                have haEq : a=(x+y)/2-2 := by omega
                have hkEq : k=(x+2*y-a-7)/2 := by omega
                exact ⟨haEq,hkEq⟩
            | succ n =>
                have hfac : 2*(a-1)+6 = 2*(a+2) := by omega
                have hfour : 4∣(2*(a-1)+6) := by
                  rw [hfac]
                  have hmod : (a+2)%2=0 := by omega
                  have hdiv : 2∣a+2 := Nat.dvd_of_mod_eq_zero hmod
                  rcases hdiv with ⟨q,hq⟩
                  refine ⟨q,?_⟩
                  rw [hq]
                  ring
                have hpowdiv : 2∣2^(n+1) := by
                  change 2^1∣2^(n+1)
                  exact Nat.pow_dvd_pow 2 (by omega)
                rcases hfour with ⟨q,hq⟩
                rcases hpowdiv with ⟨r,hr⟩
                have hdiv8 : 8∣x+y := by
                  refine ⟨r*q,?_⟩
                  rw [hpow,hr,hq]
                  ring
                have hmod : (x+y)%8=0 := Nat.mod_eq_zero_of_dvd hdiv8
                omega
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at hp
            rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hodd : (x+y+1)%2=1 := by omega
              have heven : (2^n*(2*(a-1)+8))%2=0 := by simp [Nat.mul_mod]
              rw [hpow] at hodd
              omega

/-- Even/odd outputs with x+y+1 = 12 mod 16 have only their
    depth-zero odd-left bounce predecessor. -/
private theorem even_odd_sumplus1_12_parent (a k x y : Nat)
    (hx : 5<x) (hy : 5≤y)
    (hxe : x%2=0) (hyo : y%2=1)
    (hs : (x+y+1)%16=12)
    (hedge : secNext (a,k)=some (x,y)) :
    a=(x+y+1)/2-3 ∧ k=(x+2*y-a-7)/2 := by
  have hp := (complete_section_inverse a k x y hy).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageCriterion,ha0,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageCriterion,if_pos ha0,if_neg hk0,if_neg hk1] at hp
        rcases hp with ⟨n,hpow,_⟩
        have hodd : (x+y)%2=1 := by omega
        have heven : (2^n*8)%2=0 := by simp
        rw [hpow] at hodd
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hp
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at hp
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2] at hp
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at hp
              omega
            · simp only [sectionPreimageCriterion,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
              rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hmod : (x+y+1)%16=0 := by
                  rw [hpow]
                  simp [Nat.mul_mod]
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hp
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hlow] at hp
          rcases hp with ⟨_,hyEq⟩
          have hyEven : y%2=0 := by rw [hyEq]; omega
          omega
        · by_cases haeven : a%2=0
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos haeven] at hp
            rcases hp with ⟨n,hpow,_⟩
            have hodd : (x+y)%2=1 := by omega
            have heven : (2^n*(2*(a-1)+6))%2=0 := by simp [Nat.mul_mod]
            rw [hpow] at hodd
            omega
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at hp
            rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · cases n with
              | zero =>
                  simp at hpow hcost
                  have hform : 2*(a-1)+8=2*(a+3) := by omega
                  rw [hform] at hpow
                  have haEq : a=(x+y+1)/2-3 := by omega
                  have hkEq : k=(x+2*y-a-7)/2 := by omega
                  exact ⟨haEq,hkEq⟩
              | succ n =>
                  have hfour : 4∣(2*(a-1)+8) := by
                    have hform : 2*(a-1)+8=2*(a+3) := by omega
                    rw [hform]
                    have hmod : (a+3)%2=0 := by omega
                    have hdiv : 2∣a+3 := Nat.dvd_of_mod_eq_zero hmod
                    rcases hdiv with ⟨q,hq⟩
                    refine ⟨q,?_⟩
                    rw [hq]
                    ring
                  have hpowdiv : 2∣2^(n+1) := by
                    change 2^1∣2^(n+1)
                    exact Nat.pow_dvd_pow 2 (by omega)
                  rcases hfour with ⟨q,hq⟩
                  rcases hpowdiv with ⟨r,hr⟩
                  have hdiv8 : 8∣x+y+1 := by
                    refine ⟨r*q,?_⟩
                    rw [hpow,hr,hq]
                    ring
                  have hmod : (x+y+1)%8=0 := Nat.mod_eq_zero_of_dvd hdiv8
                  have hmod4 : (x+y+1)%8=4 := by omega
                  omega

/-- A positive-time blank output cannot have odd right counter and sum 2 mod 4. -/
private theorem no_blank_odd_sum_two (x y : Nat)
    (hy : 5≤y) (hyo : y%2=1) (hs : (x+y)%4=2) :
    ¬ CReach x y := by
  intro hr
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero =>
      have hpair : (5,1)=(x,y) := by
        simpa [BB6.Agent8Section.run] using ht
      cases hpair
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          have hseed := BB6Agent38.section_output_mod4 a k x y hedge hyo hs
          cases Prod.mk.inj hseed
          omega

/-- The low first-stop target with m=4096r+1091 has a six-state inverse
    chain ending in the forbidden odd-right sum-two sector. -/
private theorem no_low_target (u : Nat) (hu : u%4=0) :
    ¬ CReach 1 (1024*u+819) := by
  intro hT
  have hTuniq : ∀ a k, secNext (a,k)=some (1,1024*u+819) →
      a=512*u+408 ∧ k=768*u+612 := by
    intro a k hedge
    have hp := odd_odd_sum4_parent a k 1 (1024*u+819)
      (by omega) (by omega) (by omega) (by omega) (by omega) hedge
    constructor <;> omega
  have hP : CReach (512*u+408) (768*u+612) :=
    cReach_of_unique_parent 1 (1024*u+819) (512*u+408) (768*u+612)
      (by omega) hTuniq hT
  have hPuniq : ∀ a k, secNext (a,k)=some (512*u+408,768*u+612) →
      a=1280*u+1018 ∧ k=384*u+305 := by
    intro a k hedge
    have hx : (512*u+408)%2=0 := by omega
    have hy : (768*u+612)%2=0 := by omega
    have hy6 : 6≤768*u+612 := by omega
    have hsum : ((512*u+408)+(768*u+612))%8≠0 := by omega
    have hp := (section_even_even_iff_affine a k
      (512*u+408) (768*u+612) hx hy hy6 hsum).mp hedge
    constructor <;> omega
  have hD : CReach (1280*u+1018) (384*u+305) :=
    cReach_of_unique_parent (512*u+408) (768*u+612)
      (1280*u+1018) (384*u+305) (by omega) hPuniq hP
  have hDuniq : ∀ a k, secNext (a,k)=some (1280*u+1018,384*u+305) →
      a=832*u+659 ∧ k=608*u+481 := by
    intro a k hedge
    have hp := even_odd_sumplus1_12_parent a k
      (1280*u+1018) (384*u+305) (by omega) (by omega)
      (by omega) (by omega) (by omega) hedge
    constructor <;> omega
  have hQ : CReach (832*u+659) (608*u+481) :=
    cReach_of_unique_parent (1280*u+1018) (384*u+305)
      (832*u+659) (608*u+481) (by omega) hDuniq hD
  have hQuniq : ∀ a k, secNext (a,k)=some (832*u+659,608*u+481) →
      a=720*u+568 ∧ k=664*u+523 := by
    intro a k hedge
    have hp := odd_odd_sum4_parent a k (832*u+659) (608*u+481)
      (by omega) (by omega) (by omega) (by omega) (by omega) hedge
    constructor <;> omega
  have hR0 : CReach (720*u+568) (664*u+523) :=
    cReach_of_unique_parent (832*u+659) (608*u+481)
      (720*u+568) (664*u+523) (by omega) hQuniq hQ
  have hR0uniq : ∀ a k, secNext (a,k)=some (720*u+568,664*u+523) →
      a=692*u+543 ∧ k=678*u+532 := by
    intro a k hedge
    have hp := even_odd_sumplus1_12_parent a k
      (720*u+568) (664*u+523) (by omega) (by omega)
      (by omega) (by omega) (by omega) hedge
    constructor <;> omega
  have hR1 : CReach (692*u+543) (678*u+532) :=
    cReach_of_unique_parent (720*u+568) (664*u+523)
      (692*u+543) (678*u+532) (by omega) hR0uniq hR0
  have hR1run : ∃ t, BB6.Agent8Section.run secNext t (some (5,1)) =
      some (692*u+543,678*u+532) := hR1
  have hy6 : 6≤678*u+532 := by omega
  have hye : (678*u+532)%2=0 := by omega
  have hzero : ((692*u+543)+(678*u+532))%8≠0 := by omega
  have hseven : ((692*u+543)+(678*u+532))%8≠7 := by omega
  have hD2run := (BB6.Agent15.blank_reach_iff_even_right
    (692*u+543) (678*u+532) hy6 hye hzero hseven).mp hR1run
  have hD2 : CReach (1370*u+1073) (339*u+265) := by
    rcases hD2run with ⟨t,ht⟩
    refine ⟨t,?_⟩
    have hx : (692*u+543)+(678*u+532)-2=1370*u+1073 := by omega
    have hy : ((678*u+532)-2)/2=339*u+265 := by omega
    simpa [hx,hy] using ht
  have hfinal : (1370*u+1073+339*u+265)%4=2 := by omega
  have hodd : (339*u+265)%2=1 := by omega
  exact no_blank_odd_sum_two (1370*u+1073) (339*u+265)
    (by omega) hodd hfinal hD2

/-- Every genuine first stopping target with m=1091 modulo 4096 is
    absent from the all-time original blank section orbit. -/
theorem first_stop_m1091_mod4096 (time m k : Nat)
    (hm : m%4096=1091)
    (hstop : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,k) := by
  have hmEq : m=4096*(m/4096)+1091 := by omega
  let r := m/4096
  have hmeq : m=4096*r+1091 := by dsimp [r]; omega
  have hpowdiv : 1024∣2^(2*m+3) := by
    change 2^10∣2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have h3m : (3*m+4)%1024=205 := by rw [hmeq]; omega
  have hsum : (k+3*m+4)%1024=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpowdiv
  have hkmod : k%1024=819 := by omega
  let u := k/1024
  have hk : k=1024*u+819 := by dsimp [u]; omega
  have hpowEq : 1024*(u+12*r+4)=2^(2*m+3) := by
    calc
      1024*(u+12*r+4)=k+3*m+4 := by rw [hk,hmeq]; omega
      _=2^(2*m+3) := hstop
  have hpowFactor : 2^(2*m+3)=1024*2^(2*m-7) := by
    calc
      2^(2*m+3)=2^(10+(2*m-7)) := by
        rw [show 2*m+3=10+(2*m-7) by omega]
      _=2^10*2^(2*m-7) := by rw [Nat.pow_add]
      _=1024*2^(2*m-7) := by norm_num
  have hU : u+12*r+4=2^(2*m-7) := by
    rw [hpowFactor] at hpowEq
    omega
  have hpowdiv4 : 4∣2^(2*m-7) := by
    change 2^2∣2^(2*m-7)
    exact Nat.pow_dvd_pow 2 (by omega)
  rcases hpowdiv4 with ⟨q,hq⟩
  have hu : u%4=0 := by
    have heq : u+12*r+4=4*q := by rw [hU,hq]
    omega
  intro hrun
  have hT : CReach 1 (1024*u+819) := by
    refine ⟨time,?_⟩
    simpa [hk] using hrun
  exact no_low_target u hu hT

#print axioms CReach
#print axioms no_low_target
#print axioms first_stop_m1091_mod4096
end BB6.Agent21Low1091

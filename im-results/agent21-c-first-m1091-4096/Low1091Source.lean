import FullSectionInverse
import Agent38SectionParity
import EvenRightUnique
import GenericSection
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 10000

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

/-- The source-certified even-right theorem reduces blank reachability
    to the direct predecessor whenever the sum residue is neither 0 nor 7. -/
private theorem cReach_even_right_parent (x y : Nat)
    (hy6 : 6≤y) (hye : y%2=0)
    (hzero : (x+y)%8≠0) (hseven : (x+y)%8≠7)
    (hr : CReach x y) :
    CReach (x+y-2) ((y-2)/2) := by
  change (∃ t, BB6.Agent8Section.run secNext t (some (5,1))=some (x,y)) at hr
  have h := (BB6.Agent15.blank_reach_iff_even_right x y hy6 hye hzero hseven).mp hr
  change CReach (x+y-2) ((y-2)/2)
  exact h

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
              rcases hp with ⟨hy3,_⟩ | ⟨_,⟨n,hpow,_⟩⟩
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
                  have haEven : a%2=0 := haeven
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
            rcases hp with ⟨hy3,_⟩ | ⟨_,⟨n,hpow,_⟩⟩
            · omega
            · have hodd : (x+y+1)%2=1 := by omega
              have heven : (2^n*(2*(a-1)+8))%2=0 := by simp [Nat.mul_mod]
              rw [hpow] at hodd
              omega

/-- Even/odd outputs with x+y+1 = 4 mod 8 have only their
    depth-zero odd-left bounce predecessor. -/
private theorem even_odd_sumplus1_mod8_4_parent (a k x y : Nat)
    (hx : 5<x) (hy : 5≤y)
    (hxe : x%2=0) (hyo : y%2=1)
    (hs : (x+y+1)%8=4)
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
              rcases hp with ⟨hy3,_⟩ | ⟨_,⟨n,hpow,_⟩⟩
              · omega
              · have hmod16 : (x+y+1)%16=0 := by
                  rw [hpow]
                  simp [Nat.mul_mod]
                have hmod8 : (x+y+1)%8=0 := by omega
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
            rcases hp with ⟨hy3,_⟩ | ⟨_,⟨n,hpow,hcost⟩⟩
            · omega
            · by_cases hn0 : n=0
              · subst n
                simp at hpow hcost
                have hform : 2*(a-1)+8=2*(a+3) := by omega
                rw [hform] at hpow
                have haEq : a=(x+y+1)/2-3 := by omega
                have hkEq : k=(x+2*y-a-7)/2 := by omega
                exact ⟨haEq,hkEq⟩
              · have hnpos : 1≤n := by omega
                have hform : 2*(a-1)+8=2*(a+3) := by omega
                have hmodlt : a%2<2 := Nat.mod_lt a (by omega)
                have haOdd : a%2=1 := by omega
                have hmod : (a+3)%2=0 := by omega
                have hdivA : 2∣a+3 := Nat.dvd_of_mod_eq_zero hmod
                rcases hdivA with ⟨q,hq⟩
                have hfour : 4∣2*(a-1)+8 := by
                  rw [hform]
                  refine ⟨q,?_⟩
                  rw [hq]
                  ring
                have hpowdiv : 2∣2^n := by
                  change 2^1∣2^n
                  exact Nat.pow_dvd_pow 2 hnpos
                rcases hfour with ⟨r,hr⟩
                rcases hpowdiv with ⟨s,hs⟩
                have hdiv8 : 8∣x+y+1 := by
                  refine ⟨s*r,?_⟩
                  rw [hpow,hform,hs,hr]
                  ring
                have hmod : (x+y+1)%8=0 := Nat.mod_eq_zero_of_dvd hdiv8
                omega

/-- A positive-time blank output cannot have odd right counter and sum 2 mod 4. -/
private theorem no_blank_odd_sum_two (x y : Nat)
    (hy : 5≤y) (hyo : y%2=1) (hs : (x+y)%4=2) :
    ¬ CReach x y := by
  intro hr
  rcases hr with ⟨time,ht⟩
  have hpair := BB6Agent38.blank_section_mod4 time x y ht hyo hs
  cases hpair
  omega

/-- The first five exact source inversions reduce every target
    (1,1024*q+819) to the even-right state shown here. -/
private theorem low_target_reaches_R1 (q : Nat)
    (hT : CReach 1 (1024*q+819)) :
    CReach (692*q+543) (678*q+532) := by
  have hTuniq : ∀ a k, secNext (a,k)=some (1,1024*q+819) →
      a=512*q+408 ∧ k=768*q+612 := by
    intro a k hedge
    have hp := odd_odd_sum4_parent a k 1 (1024*q+819)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hedge
    constructor <;> omega
  have hP : CReach (512*q+408) (768*q+612) :=
    cReach_of_unique_parent 1 (1024*q+819) (512*q+408) (768*q+612)
      (by omega) hTuniq hT
  have hPuniq : ∀ a k, secNext (a,k)=some (512*q+408,768*q+612) →
      a=1280*q+1018 ∧ k=384*q+305 := by
    intro a k hedge
    have hx : (512*q+408)%2=0 := by omega
    have hy : (768*q+612)%2=0 := by omega
    have hy6 : 6≤768*q+612 := by omega
    have hsum : ((512*q+408)+(768*q+612))%8≠0 := by omega
    have hp := (section_even_even_iff_affine a k
      (512*q+408) (768*q+612) hx hy hy6 hsum).mp hedge
    constructor <;> omega
  have hD : CReach (1280*q+1018) (384*q+305) :=
    cReach_of_unique_parent (512*q+408) (768*q+612)
      (1280*q+1018) (384*q+305) (by omega) hPuniq hP
  have hDuniq : ∀ a k, secNext (a,k)=some (1280*q+1018,384*q+305) →
      a=832*q+659 ∧ k=608*q+481 := by
    intro a k hedge
    have hp := even_odd_sumplus1_mod8_4_parent a k
      (1280*q+1018) (384*q+305) (by omega) (by omega)
      (by omega) (by omega) (by omega) hedge
    constructor <;> omega
  have hQ : CReach (832*q+659) (608*q+481) :=
    cReach_of_unique_parent (1280*q+1018) (384*q+305)
      (832*q+659) (608*q+481) (by omega) hDuniq hD
  have hQuniq : ∀ a k, secNext (a,k)=some (832*q+659,608*q+481) →
      a=720*q+568 ∧ k=664*q+523 := by
    intro a k hedge
    have hp := odd_odd_sum4_parent a k (832*q+659) (608*q+481)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hedge
    constructor <;> omega
  have hR0 : CReach (720*q+568) (664*q+523) :=
    cReach_of_unique_parent (832*q+659) (608*q+481)
      (720*q+568) (664*q+523) (by omega) hQuniq hQ
  have hR0uniq : ∀ a k, secNext (a,k)=some (720*q+568,664*q+523) →
      a=692*q+543 ∧ k=678*q+532 := by
    intro a k hedge
    have hp := even_odd_sumplus1_mod8_4_parent a k
      (720*q+568) (664*q+523) (by omega) (by omega)
      (by omega) (by omega) (by omega) hedge
    constructor <;> omega
  exact cReach_of_unique_parent (720*q+568) (664*q+523)
    (692*q+543) (678*q+532) (by omega) hR0uniq hR0

/-- The q=0 (mod 4) cylinder terminates immediately in the forbidden
    odd-right, sum-two image sector. -/
private theorem no_low_target_q0 (q : Nat) (hq : q%4=0) :
    ¬ CReach 1 (1024*q+819) := by
  intro hT
  have hR1 := low_target_reaches_R1 q hT
  have hzero : ((692*q+543)+(678*q+532))%8≠0 := by omega
  have hseven : ((692*q+543)+(678*q+532))%8≠7 := by omega
  have hD2 : CReach (1370*q+1073) (339*q+265) := by
    have h := cReach_even_right_parent (692*q+543) (678*q+532)
      (by omega) (by omega) hzero hseven hR1
    have hx : (692*q+543)+(678*q+532)-2=1370*q+1073 := by omega
    have hraw : CReach (1370*q+1073) ((678*q+530)/2) := by
      simpa [hx] using h
    have hnum : 678*q+530=2*(339*q+265) := by omega
    have hy : (678*q+530)/2=339*q+265 := by rw [hnum]; simp
    rw [hy] at hraw
    exact hraw
  have hfinal : (1370*q+1073+339*q+265)%4=2 := by omega
  have hodd : (339*q+265)%2=1 := by omega
  exact no_blank_odd_sum_two (1370*q+1073) (339*q+265)
    (by omega) hodd hfinal hD2

/-- A second direct-parent cylinder, q=11 (mod 16), terminates after
    three even-right reductions in the same forbidden image sector. -/
private theorem no_low_target_q11 (q : Nat) (hq : q%16=11) :
    ¬ CReach 1 (1024*q+819) := by
  intro hT
  have hR1 := low_target_reaches_R1 q hT
  have hR1zero : ((692*q+543)+(678*q+532))%8≠0 := by omega
  have hR1seven : ((692*q+543)+(678*q+532))%8≠7 := by omega
  have hS1 : CReach (1370*q+1073) (339*q+265) := by
    have h := cReach_even_right_parent (692*q+543) (678*q+532)
      (by omega) (by omega) hR1zero hR1seven hR1
    have hx : (692*q+543)+(678*q+532)-2=1370*q+1073 := by omega
    have hraw : CReach (1370*q+1073) ((678*q+530)/2) := by
      simpa [hx] using h
    have hnum : 678*q+530=2*(339*q+265) := by omega
    have hy : (678*q+530)/2=339*q+265 := by rw [hnum]; simp
    rw [hy] at hraw
    exact hraw
  have hS1zero : ((1370*q+1073)+(339*q+265))%8≠0 := by omega
  have hS1seven : ((1370*q+1073)+(339*q+265))%8≠7 := by omega
  have hS1red := cReach_even_right_parent (1370*q+1073) (339*q+265)
    (by omega) (by omega) hS1zero hS1seven hS1
  let v := q/16
  have hqeq : q=16*v+11 := by dsimp [v]; omega
  have hS2 : CReach (27344*v+20135) (2712*v+1996) := by
    have hx : (1370*q+1073)+(339*q+265)-2=27344*v+20135 := by
      rw [hqeq]
      omega
    have hraw : CReach (27344*v+20135) ((339*q+263)/2) := by
      simpa [hx] using hS1red
    have hnum : 339*q+263=2*(2712*v+1996) := by
      rw [hqeq]
      omega
    have hy : (339*q+263)/2=2712*v+1996 := by rw [hnum]; simp
    rw [hy] at hraw
    exact hraw
  have hS2zero : ((27344*v+20135)+(2712*v+1996))%8≠0 := by omega
  have hS2seven : ((27344*v+20135)+(2712*v+1996))%8≠7 := by omega
  have hS2red := cReach_even_right_parent (27344*v+20135) (2712*v+1996)
    (by omega) (by omega) hS2zero hS2seven hS2
  have hS3 : CReach (30056*v+22129) (1356*v+997) := by
    have hx : (27344*v+20135)+(2712*v+1996)-2=30056*v+22129 := by omega
    have hraw : CReach (30056*v+22129) ((2712*v+1994)/2) := by
      simpa [hx] using hS2red
    have hnum : 2712*v+1994=2*(1356*v+997) := by omega
    have hy : (2712*v+1994)/2=1356*v+997 := by rw [hnum]; simp
    rw [hy] at hraw
    exact hraw
  have hfinal : (30056*v+22129+1356*v+997)%4=2 := by omega
  have hodd : (1356*v+997)%2=1 := by omega
  exact no_blank_odd_sum_two (30056*v+22129) (1356*v+997)
    (by omega) hodd hfinal hS3

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
  let q := k/1024
  have hk : k=1024*q+819 := by dsimp [q]; omega
  have hpowEq : 1024*(q+12*r+4)=2^(2*m+3) := by
    calc
      1024*(q+12*r+4)=k+3*m+4 := by rw [hk,hmeq]; omega
      _=2^(2*m+3) := hstop
  have hpowFactor : 2^(2*m+3)=1024*2^(2*m-7) := by
    calc
      2^(2*m+3)=2^(10+(2*m-7)) := by
        rw [show 2*m+3=10+(2*m-7) by omega]
      _=2^10*2^(2*m-7) := by rw [Nat.pow_add]
      _=1024*2^(2*m-7) := by rfl
  have hU : q+12*r+4=2^(2*m-7) := by
    rw [hpowFactor] at hpowEq
    omega
  have hpowdiv4 : 4∣2^(2*m-7) := by
    change 2^2∣2^(2*m-7)
    exact Nat.pow_dvd_pow 2 (by omega)
  rcases hpowdiv4 with ⟨z,hz⟩
  have hq4 : q%4=0 := by
    have heq : q+12*r+4=4*z := by rw [hU,hz]
    omega
  intro hrun
  have hT : CReach 1 (1024*q+819) := by
    refine ⟨time,?_⟩
    simpa [hk] using hrun
  exact no_low_target_q0 q hq4 hT

/-- Every genuine first stopping target with m=12355 modulo 16384 is
    absent from the all-time original blank section orbit. -/
theorem first_stop_m12355_mod16384 (time m k : Nat)
    (hm : m%16384=12355)
    (hstop : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,k) := by
  have hmEq : m=16384*(m/16384)+12355 := by omega
  let r := m/16384
  have hmeq : m=16384*r+12355 := by dsimp [r]; omega
  have hpowdiv : 1024∣2^(2*m+3) := by
    change 2^10∣2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have h3m : (3*m+4)%1024=205 := by rw [hmeq]; omega
  have hsum : (k+3*m+4)%1024=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpowdiv
  have hkmod : k%1024=819 := by omega
  let q := k/1024
  have hk : k=1024*q+819 := by dsimp [q]; omega
  have hpowEq : 1024*(q+48*r+37)=2^(2*m+3) := by
    calc
      1024*(q+48*r+37)=k+3*m+4 := by rw [hk,hmeq]; omega
      _=2^(2*m+3) := hstop
  have hpowFactor : 2^(2*m+3)=1024*2^(2*m-7) := by
    calc
      2^(2*m+3)=2^(10+(2*m-7)) := by
        rw [show 2*m+3=10+(2*m-7) by omega]
      _=2^10*2^(2*m-7) := by rw [Nat.pow_add]
      _=1024*2^(2*m-7) := by rfl
  have hQ : q+48*r+37=2^(2*m-7) := by
    rw [hpowFactor] at hpowEq
    omega
  have hpowdiv16 : 16∣2^(2*m-7) := by
    change 2^4∣2^(2*m-7)
    exact Nat.pow_dvd_pow 2 (by omega)
  rcases hpowdiv16 with ⟨z,hz⟩
  have hq16 : q%16=11 := by
    have heq : q+48*r+37=16*z := by rw [hQ,hz]
    omega
  intro hrun
  have hT : CReach 1 (1024*q+819) := by
    refine ⟨time,?_⟩
    simpa [hk] using hrun
  exact no_low_target_q11 q hq16 hT

#print axioms low_target_reaches_R1
#print axioms no_low_target_q0
#print axioms no_low_target_q11
#print axioms first_stop_m1091_mod4096
#print axioms first_stop_m12355_mod16384
end BB6.Agent21Low1091


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
        rcases hp with ⟨n,⟨hpow,_⟩⟩
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
              rcases hp with ⟨n,⟨hpow,_⟩⟩
              have hodd : (x+y+1)%2=1 := by omega
              have heven : (2^n*16)%2=0 := by simp [Nat.mul_mod]
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
            rcases hp with ⟨n,⟨hpow,hcost⟩⟩
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
                  omega
                have hpowdiv : 2∣2^(n+1) := by
                  change 2^1∣2^(n+1)
                  exact Nat.pow_dvd_pow 2 (by omega)
                rcases hfour with ⟨q,hq⟩
                rcases hpowdiv with ⟨r,hr⟩
                have hdiv8 : 8∣x+y := by
                  refine ⟨r*q,?_⟩
                  rw [hpow,hr,hq]
                  simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
                have hmod : (x+y)%8=0 := Nat.mod_eq_zero_of_dvd hdiv8
                omega
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at hp
            rcases hp with ⟨n,⟨hpow,_⟩⟩
            have hodd : (x+y+1)%2=1 := by omega
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
        rcases hp with ⟨n,⟨hpow,_⟩⟩
        have hodd : (x+y)%2=1 := by omega
        have heven : (2^n*8)%2=0 := by simp [Nat.mul_mod]
        rw [hpow] at hodd
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
              rcases hp with ⟨n,⟨hpow,_⟩⟩
              have hmod16 : (x+y+1)%16=0 := by
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
            rcases hp with ⟨n,⟨hpow,_⟩⟩
            have hodd : (x+y)%2=1 := by omega
            have heven : (2^n*(2*(a-1)+6))%2=0 := by simp [Nat.mul_mod]
            rw [hpow] at hodd
            omega
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at hp
            rcases hp with ⟨n,⟨hpow,hcost⟩⟩
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
              omega
            have hn0 : n = 0 := by
              by_cases hzero : n = 0
              · exact hzero
              · have hnpos : 1 ≤ n := by omega
                have hpowdiv : 2 ∣ 2^n := by
                  change 2^1 ∣ 2^n
                  exact Nat.pow_dvd_pow 2 hnpos
                rcases hfour with ⟨r,hr⟩
                rcases hpowdiv with ⟨s,hs⟩
                have hdiv8 : 8 ∣ x+y+1 := by
                  refine ⟨s*r,?_⟩
                  rw [hpow,hs,hr]
                  simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
                have hmod8 : (x+y+1)%8=0 := Nat.mod_eq_zero_of_dvd hdiv8
                omega
            subst n
            simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_zero, Nat.add_zero] at hpow hcost
            rw [hform] at hpow
            have haEq : a=(x+y+1)/2-3 := by omega
            have hkEq : k=(x+2*y-a-7)/2 := by omega
            exact ⟨haEq,hkEq⟩

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


/-! A new exact first-stop exclusion on the m = 6723 (mod 8192) cylinder.
    This specializes the m = 512z+67 second fan to z = 13 (mod 16):
    v2(519z+73)=2, and both possible parents of the forced state are in
    the source-forbidden odd-right/sum-two image class. -/

private theorem low6723_succ_le_pow2 (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

def low6723M (t : Nat) : Nat := 8192*t+6723
def low6723Z (t : Nat) : Nat := 16*t+13
def low6723W (t : Nat) : Nat :=
  2^(2*low6723M t-1) - (96*low6723Z t+13)
def low6723V (t : Nat) : Nat := low6723W t / 64
def low6723H (t : Nat) : Nat :=
  173*2^(2*low6723M t-8) - (2076*t+1705)
def low6723K (t : Nat) : Nat :=
  2^(2*low6723M t+3) - (3*low6723M t+4)

private theorem low6723_params (t : Nat) :
    low6723M t = 512*low6723Z t+67 ∧
    low6723W t = 64*low6723V t+19 ∧
    low6723V t+24*t+20 = 2^(2*low6723M t-7) := by
  let m := low6723M t
  let z := low6723Z t
  let w := low6723W t
  let v := low6723V t
  have hm : m=512*z+67 := by
    dsimp [m,z,low6723M,low6723Z]
    omega
  have hc : 96*z+13≤m := by
    rw [hm]
    dsimp [z,low6723Z]
    omega
  have hlt : 2*m-2 < 2^(2*m-2) := by
    have h := low6723_succ_le_pow2 (2*m-2)
    omega
  have hpowEq : 2^(2*m-1)=2*2^(2*m-2) := by
    calc
      2^(2*m-1)=2^((2*m-2)+1) := by congr 1 <;> omega
      _=2^(2*m-2)*2 := by rw [Nat.pow_succ]
      _=2*2^(2*m-2) := by simp [Nat.mul_comm]
  have hmul := Nat.mul_lt_mul_of_pos_left hlt (by omega)
  rw [hpowEq] at hmul
  have hPowBig : 2*m < 2^(2*m-1) := by omega
  have hbig : 96*z+13≤2^(2*m-1) := by omega
  have hdiff : w+(96*z+13)=2^(2*m-1) := by
    dsimp [w,low6723W]
    exact Nat.sub_add_cancel hbig
  have hpowdiv : 64∣2^(2*m-1) := by
    change 2^6∣2^(2*m-1)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpmod : (2^(2*m-1))%64=0 :=
    Nat.mod_eq_zero_of_dvd hpowdiv
  have hcmod : (96*z+13)%64=45 := by
    dsimp [z,low6723Z]
    omega
  have hsumMod : (w+(96*z+13))%64=0 := by
    rw [hdiff,hpmod]
  rw [Nat.add_mod] at hsumMod
  have hwlt : w%64<64 := Nat.mod_lt w (by omega)
  have hwmod : w%64=19 := by omega
  have hW : w=64*v+19 := by
    have h := Nat.mod_add_div w 64
    dsimp [v,low6723V]
    omega
  have hcExpr : 96*z+13=64*(24*t+19)+45 := by
    dsimp [z,low6723Z]
    omega
  have hpowFactor : 2^(2*m-1)=64*2^(2*m-7) := by
    calc
      2^(2*m-1)=2^(6+(2*m-7)) := by congr 1 <;> omega
      _=2^6*2^(2*m-7) := by rw [Nat.pow_add]
      _=64*2^(2*m-7) := by simp [Nat.mul_comm]
  have hvEq : v+24*t+20=2^(2*m-7) := by
    rw [hW,hcExpr,hpowFactor] at hdiff
    omega
  exact ⟨hm,hW,hvEq⟩

private theorem no_blank_odd_sum_two_ne51 (x y : Nat)
    (hr : CReach x y) (hyo : y%2=1)
    (hs : (x+y)%4=2) (hne : (x,y)≠(5,1)) : False := by
  rcases hr with ⟨time,ht⟩
  have hpair := BB6Agent38.blank_section_mod4 time x y ht hyo hs
  exact hne hpair

/-- Every parent of the special R-state is in the source-forbidden
    odd-right/sum-two class. -/
private theorem low6723_parent_mod4 (a k x y H : Nat)
    (hx : 5<x) (hy : 5≤y)
    (hxe : x%2=0) (hyo : y%2=1)
    (hT : x+y+1=16*H) (hH4 : H%4=3)
    (hU : (x+2*y)%8=6)
    (hedge : secNext (a,k)=some (x,y)) :
    k%2=1 ∧ (a+k)%4=2 ∧ a<2*k := by
  have hp := (complete_section_inverse a k x y hy).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageCriterion,ha0,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageCriterion,if_pos ha0,if_neg hk0,if_neg hk1] at hp
        rcases hp with ⟨n,⟨hpow,_⟩⟩
        have hodd : (x+y)%2=1 := by omega
        have heven : (2^n*8)%2=0 := by simp [Nat.mul_mod]
        rw [hpow] at hodd
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
              rcases hp with ⟨n,⟨hpow,_⟩⟩
              have hEq : H=2^n := by
                rw [hT] at hpow
                omega
              have hHodd : H%2=1 := by omega
              cases n with
              | zero =>
                  simp at hEq
                  omega
              | succ n =>
                  rw [hEq] at hHodd
                  simp at hHodd
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
            rcases hp with ⟨n,⟨hpow,_⟩⟩
            have hodd : (x+y)%2=1 := by omega
            have heven : (2^n*(2*(a-1)+6))%2=0 := by
              simp [Nat.mul_mod]
            rw [hpow] at hodd
            omega
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at hp
            rcases hp with ⟨n,⟨hpow,hcost⟩⟩
            have hform : 2*(a-1)+8=2*(a+3) := by omega
            have hmod : (a+3)%2=0 := by omega
            have hdivA : 2∣a+3 := Nat.dvd_of_mod_eq_zero hmod
            rcases hdivA with ⟨q,hq⟩
            have hfour : 4∣2*(a-1)+8 := by
              rw [hform]
              refine ⟨q,?_⟩
              rw [hq]
              omega
            have hn : n≤2 := by
              by_contra h
              have hn3 : 3≤n := by omega
              have hpowdiv8 : 8∣2^n := by
                change 2^3∣2^n
                exact Nat.pow_dvd_pow 2 hn3
              rcases hpowdiv8 with ⟨p,hp⟩
              rcases hfour with ⟨q,hq⟩
              have hdiv32 : 32∣x+y+1 := by
                refine ⟨p*q,?_⟩
                rw [hpow,hp,hq]
                simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
              have hmod0 : (x+y+1)%32=0 :=
                Nat.mod_eq_zero_of_dvd hdiv32
              have hHodd : H%2=1 := by omega
              have hHdecomp : H=2*(H/2)+1 := by
                have h := Nat.mod_add_div H 2
                omega
              have hmod16 : (x+y+1)%32=16 := by
                rw [hT,hHdecomp]
                omega
              omega
            have haOdd : a%2=1 := by
              have hlt : a%2<2 := Nat.mod_lt a (by omega)
              omega
            have hcost' : 2*k+a+7+3*n=x+2*y := by omega
            have hnEven : n%2=0 := by omega
            have hnCases : n=0 ∨ n=2 := by omega
            rcases hnCases with hn0 | hn2
            · subst n
              simp at hpow hcost
              rw [hform] at hpow
              have haEq : a+3=8*H := by
                rw [hT] at hpow
                omega
              have ha8 : a%8=5 := by omega
              have hk4 : k%4=1 := by omega
              have hsum : (a+k)%4=2 := by omega
              exact ⟨by omega,hsum,by omega⟩
            · subst n
              simp at hpow hcost
              rw [hform] at hpow
              have haEq : a+3=2*H := by
                rw [hT] at hpow
                omega
              have ha8 : a%8=3 := by omega
              have hk4 : k%4=3 := by omega
              have hsum : (a+k)%4=2 := by omega
              exact ⟨by omega,hsum,by omega⟩

private theorem low6723_R_unreachable (t : Nat) :
    ¬ CReach (720*low6723V t+208) (664*low6723V t+191) := by
  let m := low6723M t
  let v := low6723V t
  let x := 720*v+208
  let y := 664*v+191
  let H := low6723H t
  let q := 2076*t+1705
  have hparams := low6723_params t
  rcases hparams with ⟨hm,hW,hvEq⟩
  have hqleExp : q≤2*m-8 := by
    dsimp [q,m,low6723M]
    omega
  have hpowgt : 2*m-8<2^(2*m-8) := by
    have h := low6723_succ_le_pow2 (2*m-8)
    omega
  have hqle : q≤173*2^(2*m-8) := by omega
  have hHplus : H+q=173*2^(2*m-8) := by
    dsimp [H,low6723H]
    exact Nat.sub_add_cancel hqle
  have hpowdiv4 : 4∣2^(2*m-8) := by
    change 2^2∣2^(2*m-8)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod4 : (2^(2*m-8))%4=0 :=
    Nat.mod_eq_zero_of_dvd hpowdiv4
  have hfirstmod : (173*2^(2*m-8))%4=0 := by
    rw [Nat.mul_mod,hpowmod4]
    norm_num
  have hqmod : q%4=1 := by
    dsimp [q]
    omega
  have hHmod : H%4=3 := by
    have hsum : (H+q)%4=0 := by rw [hHplus,hfirstmod]
    rw [Nat.add_mod,hqmod] at hsum
    omega
  have hpow16 : 2^(2*m-4)=16*2^(2*m-8) := by
    calc
      2^(2*m-4)=2^(4+(2*m-8)) := by congr 1 <;> omega
      _=2^4*2^(2*m-8) := by rw [Nat.pow_add]
      _=16*2^(2*m-8) := by simp [Nat.mul_comm]
  have hH16 : 16*H+16*q=173*2^(2*m-4) := by
    calc
      16*H+16*q=16*(H+q) := by omega
      _=16*(173*2^(2*m-8)) := by rw [hHplus]
      _=173*(16*2^(2*m-8)) := by simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
      _=173*2^(2*m-4) := by rw [hpow16]
  have hpow8 : 2^(2*m-4)=8*2^(2*m-7) := by
    calc
      2^(2*m-4)=2^(3+(2*m-7)) := by congr 1 <;> omega
      _=2^3*2^(2*m-7) := by rw [Nat.pow_add]
      _=8*2^(2*m-7) := by simp [Nat.mul_comm]
  have hTplus : x+y+1+16*q=173*2^(2*m-4) := by
    dsimp [x,y]
    rw [hpow8,hvEq]
    omega
  have hT : x+y+1=16*H := by omega
  have hU : (x+2*y)%8=6 := by
    dsimp [x,y]
    omega
  have hx : 5<x := by dsimp [x]; omega
  have hy : 5≤y := by dsimp [y]; omega
  have hxe : x%2=0 := by dsimp [x]; omega
  have hyo : y%2=1 := by dsimp [y]; omega
  intro hr
  obtain ⟨a,k,hrp,hedge⟩ := cReach_parent_of_right5 x y hy hr
  have hpar := low6723_parent_mod4 a k x y H hx hy hxe hyo hT hHmod hU hedge
  have hne : (a,k)≠(5,1) := by
    intro h
    cases Prod.mk.inj h
    omega
  exact no_blank_odd_sum_two_ne51 a k hrp hpar.1 hpar.2.1 hne

private theorem low6723_target_reaches_R (t : Nat)
    (hT : CReach 1 (low6723K t)) :
    CReach (720*low6723V t+208) (664*low6723V t+191) := by
  let m := low6723M t
  let z := low6723Z t
  let w := low6723W t
  let v := low6723V t
  let K := low6723K t
  have hparams := low6723_params t
  rcases hparams with ⟨hm,hW,hvEq⟩
  have hlt : 2*m<2^(2*m) := by
    have h := low6723_succ_le_pow2 (2*m)
    omega
  have hpow8 : 2^(2*m+3)=8*2^(2*m) := by
    calc
      2^(2*m+3)=2^(2*m+3) := rfl
      _=2^(2*m)*2^3 := by rw [Nat.pow_add]
      _=8*2^(2*m) := by simp [Nat.mul_comm]
  have hle : 3*m+4≤2^(2*m+3) := by rw [hpow8]; omega
  have hKadd : K+3*m+4=2^(2*m+3) := by
    dsimp [K,low6723K]
    exact Nat.sub_add_cancel hle
  have hpowdiv1024 : 1024∣2^(2*m+3) := by
    change 2^10∣2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod1024 : (2^(2*m+3))%1024=0 :=
    Nat.mod_eq_zero_of_dvd hpowdiv1024
  have h3m1024 : (3*m+4)%1024=717 := by
    rw [hm]
    dsimp [z,low6723Z]
    omega
  have hKmod : K%1024=307 := by
    have hsum : (K+3*m+4)%1024=0 := by rw [hKadd,hpowmod1024]
    rw [Nat.add_mod,h3m1024] at hsum
    omega
  have hKge : 5≤K := by omega
  have hKodd : K%2=1 := by omega
  have hpowdiv8 : 8∣2^(2*m+3) := by
    change 2^3∣2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod8 : (2^(2*m+3))%8=0 :=
    Nat.mod_eq_zero_of_dvd hpowdiv8
  have h3m3 : (3*m+3)%8=4 := by
    rw [hm]
    dsimp [z,low6723Z]
    omega
  have hsum8 : (1+K)%8=4 := by
    have hsum : ((1+K)+(3*m+3))%8=0 := by
      have hEq : (1+K)+(3*m+3)=2^(2*m+3) := by omega
      rw [hEq,hpowmod8]
    rw [Nat.add_mod,h3m3] at hsum
    omega
  have hPuniq : ∀ a k, secNext (a,k)=some (1,K) →
      a=8*w ∧ k=12*w := by
    intro a k hedge
    have hp := odd_odd_sum4_parent a k 1 K
      (by omega) (by omega) hKge (by omega) hKodd hsum8 hedge
    rcases hp with ⟨ha,hk⟩
    have hpow1024 : 2^(2*m+3)=1024*2^(2*m-7) := by
      calc
        2^(2*m+3)=2^(10+(2*m-7)) := by congr 1 <;> omega
        _=2^10*2^(2*m-7) := by rw [Nat.pow_add]
        _=1024*2^(2*m-7) := by simp [Nat.mul_comm]
    have hP1sum : 2*(8*w+2)+(3*m+3)=2^(2*m+3) := by
      rw [hW,hpow1024,hm]
      omega
    have hKsum : (1+K)+(3*m+3)=2^(2*m+3) := by omega
    have hP1 : 2*(8*w+2)=1+K := by omega
    have hpow2048 : 2^(2*m+4)=2048*2^(2*m-7) := by
      calc
        2^(2*m+4)=2^(11+(2*m-7)) := by congr 1 <;> omega
        _=2^11*2^(2*m-7) := by rw [Nat.pow_add]
        _=2048*2^(2*m-7) := by simp [Nat.mul_comm]
    have hP2sum : 32*w+6+6*m+8=2^(2*m+4) := by
      rw [hW,hpow2048,hm]
      omega
    have hdouble : 2*2^(2*m+3)=2^(2*m+4) := by
      calc
        2*2^(2*m+3)=2^(2*m+3)*2 := by simp [Nat.mul_comm]
        _=2^(2*m+3+1) := by rw [← Nat.pow_succ]
        _=2^(2*m+4) := by congr 1 <;> omega
    have hK2sum : 2*K+6*m+8=2^(2*m+4) := by
      calc
        2*K+6*m+8=2*(K+3*m+4) := by omega
        _=2*2^(2*m+3) := by rw [hKadd]
        _=2^(2*m+4) := hdouble
    have hP2 : 2*K=32*w+6 := by omega
    constructor <;> omega
  have hP : CReach (8*w) (12*w) :=
    cReach_of_unique_parent 1 K (8*w) (12*w) (by omega) hPuniq hT
  have hPzero : (8*w+12*w)%8≠0 := by rw [hW]; omega
  have hPseven : (8*w+12*w)%8≠7 := by rw [hW]; omega
  have hD0 := cReach_even_right_parent (8*w) (12*w)
    (by omega) (by omega) (by omega) hPzero hPseven hP
  have hD : CReach (20*w-2) (6*w-1) := by
    have hx : 8*w+12*w-2=20*w-2 := by omega
    have hraw : CReach (20*w-2) ((12*w-2)/2) := by
      simpa [hx] using hD0
    have hnum : 12*w-2=2*(6*w-1) := by omega
    have hy : (12*w-2)/2=6*w-1 := by rw [hnum]; simp
    rw [hy] at hraw
    exact hraw
  have hDuniq : ∀ a k, secNext (a,k)=some (20*w-2,6*w-1) →
      a=13*w-4 ∧ k=(19*w-7)/2 := by
    intro a k hedge
    have hs : ((20*w-2)+(6*w-1)+1)%8=4 := by rw [hW]; omega
    have hp := even_odd_sumplus1_mod8_4_parent a k
      (20*w-2) (6*w-1) (by omega) (by omega)
      (by omega) (by omega) hs hedge
    constructor <;> omega
  have hQ : CReach (13*w-4) ((19*w-7)/2) :=
    cReach_of_unique_parent (20*w-2) (6*w-1)
      (13*w-4) ((19*w-7)/2) (by omega) hDuniq hD
  have hQx : 13*w-4=832*v+243 := by rw [hW]; omega
  have hQy : (19*w-7)/2=608*v+177 := by rw [hW]; omega
  have hQsum : ((13*w-4)+(19*w-7)/2)%8=4 := by
    rw [hQx,hQy]
    omega
  have hQuniq : ∀ a k, secNext (a,k)=some (13*w-4,(19*w-7)/2) →
      a=720*v+208 ∧ k=664*v+191 := by
    intro a k hedge
    have hp := odd_odd_sum4_parent a k (13*w-4) ((19*w-7)/2)
      (by rw [hQx]; omega) (by rw [hQx]; omega)
      (by rw [hQy]; omega) (by rw [hQx]; omega)
      (by rw [hQy]; omega) hQsum hedge
    rcases hp with ⟨ha,hk⟩
    rw [hQx,hQy] at ha hk
    constructor <;> omega
  exact cReach_of_unique_parent (13*w-4) ((19*w-7)/2)
    (720*v+208) (664*v+191) (by omega) hQuniq hQ

/-- Every first stopping target with m=6723 (mod 8192) is absent
    from the all-time original blank section orbit. -/
theorem first_stop_m6723_mod8192 (time m k : Nat)
    (hm : m%8192=6723)
    (hstop : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,k) := by
  intro hrun
  have hmEq : m=8192*(m/8192)+6723 := by omega
  let t := m/8192
  have hmeq : m=8192*t+6723 := by dsimp [t]; omega
  have hlt : 2*m<2^(2*m) := by
    have h := low6723_succ_le_pow2 (2*m)
    omega
  have hpow : 2^(2*m+3)=8*2^(2*m) := by
    calc
      2^(2*m+3)=2^(2*m+3) := rfl
      _=2^(2*m)*2^3 := by rw [Nat.pow_add]
      _=8*2^(2*m) := by simp [Nat.mul_comm]
  have hle : 3*m+4≤2^(2*m+3) := by rw [hpow]; omega
  have hK : k=2^(2*m+3)-(3*m+4) := by omega
  have hT : CReach 1 (low6723K t) := by
    refine ⟨time,?_⟩
    dsimp [low6723K,low6723M]
    rw [hmeq,hK]
    exact hrun
  have hR := low6723_target_reaches_R t hT
  exact low6723_R_unreachable t hR

#print axioms first_stop_m6723_mod8192


#print axioms first_stop_m12355_mod16384
end BB6.Agent21Low1091


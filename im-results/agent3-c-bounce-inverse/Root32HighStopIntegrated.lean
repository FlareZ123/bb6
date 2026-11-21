import U5B2Root32
import U5Y3ParentFan
import D0EInverseArithmetic
import Root32HighStopIndexMap
import OddOddLowVal
import OddOddVal3Orbit
import Agent3CImage
import MixedOdd16TwoOrbit
import EvenRightUnique
import HighSumTwo
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

namespace BB6.Agent3Root32HighStopIntegrated
open BB6.Agent46

/-- Explicit blank-section return predicate, kept in run form so
source-parent transports do not unfold a reachability wrapper. -/
def RunReach (x y : Nat) : Prop :=
  ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) = some (x,y)

/-- Every non-seed blank return has a blank-reachable immediate source
parent. This is the run-level form of the shared section predecessor lemma. -/
theorem run_parent_of_left_gt5 (x y : Nat) (hx : 5<x)
    (hr : RunReach x y) :
    ∃ a k, RunReach a k ∧ secNext (a,k)=some (x,y) := by
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at ht
    | some p =>
      rcases p with ⟨a,k⟩
      refine ⟨a,k,⟨n,hp⟩,?_⟩
      simpa [BB6.Agent8Section.run,hp] using ht

/-- The source-certified odd-image invariant excludes odd-right returns
whose coordinate sum is two modulo four. -/
theorem run_no_odd_sum_two (x y : Nat)
    (hx : 5<x) (hy : 5≤y) (ho : y%2=1)
    (hsum : (x+y)%4=2) : ¬ RunReach x y := by
  intro hr
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    have hi := BB6.Agent3.blank_section_odd_image n x y ht hy ho
    omega

/-- An even/odd target with odd total sum and sum-plus-one exactly
four modulo eight has a unique source parent: the odd-a depth-zero
branch. This is the common local gate used in the high-stop inverse. -/
theorem evenodd_sumplusone_v2two_parent (x y a k : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy8 : 8<y)
    (hsum : (x+y)%2=1) (hval : (x+y+1)%8=4)
    (hedge : secNext (a,k)=some (x,y)) :
    a=(x+y+1)/2-3 ∧ k=(x+2*y-a-7)/2 := by
  have hp := (section_preimage_all_iff a k x y).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hxy,_⟩
        have heven : (x+y)%2=0 := by rw [hxy]; simp [Nat.mul_mod]
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp <;> omega
            · have hcase :
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat,
                    x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hzero : (x+y+1)%8=0 := by
                  rw [hpow]
                  simp [Nat.mul_mod]
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hpow,_⟩
            have heven : (x+y)%2=0 := by
              rw [hpow]
              simp [Nat.mul_mod]
            omega
          · have haodd : a%2=1 := by omega
            have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat,
                  x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have hfac4 : 4 ∣ 2*(a-1)+8 := by
                have hAeven : (a+3)%2=0 := by omega
                obtain ⟨q,hq⟩ := Nat.dvd_of_mod_eq_zero hAeven
                refine ⟨q,?_⟩
                omega
              by_cases hn : n=0
              · subst n
                have hmain : x+y+1=2*a+6 := by omega
                have hquot : (x+y+1)/2=a+3 := by omega
                have hcost' : 2*k+a+7=x+2*y := by omega
                constructor <;> omega
              · have hnpos : 1≤n := by omega
                have hpowdiv : 2 ∣ 2^n := by
                  have hdiv : 2^1 ∣ 2^n := Nat.pow_dvd_pow 2 hnpos
                  simpa using hdiv
                rcases hpowdiv with ⟨p,hp2⟩
                rcases hfac4 with ⟨q,hq4⟩
                have hdiv8 : 8 ∣ 2^n*(2*(a-1)+8) := by
                  refine ⟨p*q,?_⟩
                  rw [hp2,hq4]
                  ac_rfl
                have hzero : (x+y+1)%8=0 := by
                  rw [hpow]
                  exact Nat.mod_eq_zero_of_dvd hdiv8
                omega

/-- On the exact u=1802+6720*t progression, a blank visit to the
high-stop target T forces a visit to Q. The q>=1 U5 parent branch is
eliminated by the odd-sum-two blank-image theorem. -/
theorem T_reach_implies_Q_reach (u : Nat) (hu7 : u%7=3)
    (hT : RunReach (1048576*u+70538) 3) :
    RunReach (524288*u+35269) (262144*u+17635) := by
  let m := 4408+65536*u
  have hm7 : (m+1)%7=5 := by dsimp [m]; omega
  obtain ⟨a,k,hprev,hstep⟩ := run_parent_of_left_gt5
    (1048576*u+70538) 3 (by omega) hT
  have htarget : 16*m+10=1048576*u+70538 := by dsimp [m]; omega
  have hstep' : secNext (a,k)=some (16*m+10,3) := by
    simpa only [htarget] using hstep
  have hfan := BB6.Agent3U5DepthFan.y3_u5_parent_fan m a k hm7 hstep'
  rcases hfan with hq0 | ⟨q,U,hq,hpow,hdecomp,hA,hK⟩
  · have hA' : a=524288*u+35269 := by
      have h := hq0.1
      dsimp [m] at h
      omega
    have hK' : k=262144*u+17635 := by
      have h := hq0.2
      dsimp [m] at h
      omega
    simpa only [hA',hK'] using hprev
  · have hmEven : m%2=0 := by dsimp [m]; omega
    have hm1Odd : (m+1)%2=1 := by omega
    by_cases hq1 : q=1
    · subst q
      have hdecomp' : m+1=U := by simpa using hdecomp
      have hA' : a=2*m-1 := by omega
      have hK' : k=7*m+3 := by omega
      have hright : 5≤k := by rw [hK']; omega
      have hodd : k%2=1 := by rw [hK']; omega
      have hsum : (a+k)%4=2 := by rw [hA',hK']; omega
      exact False.elim (run_no_odd_sum_two a k (by omega) hright hodd hsum hprev)
    · have hq2 : 2≤q := by omega
      have hexp : 1≤2*q-2 := by omega
      have hdiv : 2^1 ∣ 2^(2*q-2) := Nat.pow_dvd_pow 2 hexp
      have hpowEven : (2^(2*q-2))%2=0 := by
        have hdiv' : 2 ∣ 2^(2*q-2) := by simpa using hdiv
        exact Nat.mod_eq_zero_of_dvd hdiv'
      have hmod' : (m+1)%2=0 := by rw [hdecomp]; simp [Nat.mul_mod,hpowEven]
      omega

/-- Q has a unique source parent by the valuation-three source
parent equations; a blank return therefore propagates to S3. -/
theorem Q_reach_implies_S3_reach (u : Nat) (huEven : u%2=0)
    (hQ : RunReach (524288*u+35269) (262144*u+17635)) :
    RunReach (393216*u+26450) (327680*u+22041) := by
  have hx : (524288*u+35269)%2=1 := by omega
  have hy : (262144*u+17635)%2=1 := by omega
  have hy5 : 5≤262144*u+17635 := by omega
  have hsumEq : (524288*u+35269)+(262144*u+17635)=786432*u+52904 := by omega
  have hsum16 : ((524288*u+35269)+(262144*u+17635))%16=8 := by
    rw [hsumEq]
    omega
  have hsize : 24≤(524288*u+35269)+(262144*u+17635) := by
    rw [hsumEq]
    omega
  obtain ⟨a,k,hprev,hstep⟩ := run_parent_of_left_gt5
    (524288*u+35269) (262144*u+17635) (by omega) hQ
  have heq := BB6.Agent3.oddodd_val3_parent_equations
    a k (524288*u+35269) (262144*u+17635) hx hy hy5 hsum16 hsize hstep
  rcases heq with ⟨hxy,hcost⟩
  have haEq : a=393216*u+26450 := by omega
  have hkEq : k=327680*u+22041 := by omega
  simpa only [haEq,hkEq] using hprev

/-- The even/odd sum-plus-one gate fixes the sole parent of S3. -/
theorem S3_reach_implies_S2_reach (u : Nat)
    (hS3 : RunReach (393216*u+26450) (327680*u+22041)) :
    RunReach (360448*u+24243) (344064*u+23141) := by
  obtain ⟨a,k,hprev,hstep⟩ := run_parent_of_left_gt5
    (393216*u+26450) (327680*u+22041) (by omega) hS3
  have hx : (393216*u+26450)%2=0 := by omega
  have hy : (327680*u+22041)%2=1 := by omega
  have hy8 : 8<327680*u+22041 := by omega
  have hsumEq : (393216*u+26450)+(327680*u+22041)=720896*u+48491 := by omega
  have hsum : ((393216*u+26450)+(327680*u+22041))%2=1 := by
    rw [hsumEq]
    omega
  have hval : ((393216*u+26450)+(327680*u+22041)+1)%8=4 := by
    rw [hsumEq]
    have hplus : 720896*u+48491+1=720896*u+48492 := by rfl
    rw [hplus]
    rw [show 720896=8*90112 by decide, show 48492=8*6061+4 by decide]
    simp [Nat.add_mod,Nat.mul_mod]
  obtain ⟨ha,hk⟩ := evenodd_sumplusone_v2two_parent
    (393216*u+26450) (327680*u+22041) a k hx hy hy8 hsum hval hstep
  have haEq : a=360448*u+24243 := by omega
  have hkEq : k=344064*u+23141 := by omega
  simpa only [haEq,hkEq] using hprev

/-- S2 has a unique source parent by the valuation-three source
parent equations; a blank return therefore propagates to S1. -/
theorem S2_reach_implies_S1_reach (u : Nat) (huEven : u%2=0)
    (hS2 : RunReach (360448*u+24243) (344064*u+23141)) :
    RunReach (352256*u+23690) (348160*u+23414) := by
  have hx : (360448*u+24243)%2=1 := by omega
  have hy : (344064*u+23141)%2=1 := by omega
  have hy5 : 5≤344064*u+23141 := by omega
  have hsumEq : (360448*u+24243)+(344064*u+23141)=704512*u+47384 := by omega
  have hsum16 : ((360448*u+24243)+(344064*u+23141))%16=8 := by
    rw [hsumEq]
    omega
  have hsize : 24≤(360448*u+24243)+(344064*u+23141) := by
    rw [hsumEq]
    omega
  obtain ⟨a,k,hprev,hstep⟩ := run_parent_of_left_gt5
    (360448*u+24243) (344064*u+23141) (by omega) hS2
  have heq := BB6.Agent3.oddodd_val3_parent_equations
    a k (360448*u+24243) (344064*u+23141) hx hy hy5 hsum16 hsize hstep
  rcases heq with ⟨hxy,hcost⟩
  have haEq : a=352256*u+23690 := by omega
  have hkEq : k=348160*u+23414 := by omega
  simpa only [haEq,hkEq] using hprev

end BB6.Agent3Root32HighStopIntegrated

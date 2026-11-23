import Root32HighStopA4Core
import Root32HighStopR10592Core
import RRoot32ParentFanQ
import OddOddLowVal
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent6RRoot32Q3Closure

open BB6.Agent46
open BB6.Agent3RRoot32ParentFanQ

abbrev RunReach (x y : Nat) : Prop :=
  BB6.Agent3Root32HighStopA4Core.RunReach x y

private theorem toCReach (x y : Nat) (h : RunReach x y) :
    BB6.Agent3.CReach x y := by
  simpa [RunReach, BB6.Agent3Root32HighStopA4Core.RunReach,
    BB6.Agent3.CReach] using h

private theorem ofCReach (x y : Nat) (h : BB6.Agent3.CReach x y) :
    RunReach x y := by
  simpa [RunReach, BB6.Agent3Root32HighStopA4Core.RunReach,
    BB6.Agent3.CReach] using h

/-- The q=3 (mod 8) R-parent fan. Its valuation data are the same
as the q=7 (mod 64) fan, but this is a separate residue cylinder. -/
private theorem R_parent_fan_q3 (q a k : Nat)
    (hq : q%8=3)
    (hstep : secNext (a,k)=some (RxQ q,RyQ q)) :
    (a=RpxQ q ∧ k=RpyQ q) ∨
    (a=AbxQ q ∧ k=AbyQ q) := by
  let x := RxQ q
  let y := RyQ q
  have hx : 5<x := by dsimp [x,RxQ]; omega
  have hy : 6≤y := by dsimp [y,RyQ]; omega
  have hye : y%2=0 := by dsimp [y,RyQ]; omega
  have hsum8 : (x+y)%8=7 := by
    dsimp [x,y,RxQ,RyQ]
    omega
  have hplus16 : (x+y+1)%16=8 := by
    dsimp [x,y,RxQ,RyQ]
    omega
  have hCodd : (x+2*y)%2=1 := by
    dsimp [x,y,RxQ,RyQ]
    omega
  have hp := (section_preimage_all_iff a k x y).mp hstep
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp <;> omega
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp <;> omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hpow,hcost⟩
        have hzero : (x+y)%8=0 := by rw [hpow]; simp [Nat.mul_mod]
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
                  (5≤y ∧ ∃ n : Nat, x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hzero : (x+y+1)%16=0 := by
                  rw [hpow]
                  simp [Nat.mul_mod]
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨_,hyy⟩
          omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hpow,_⟩
            have hzero : (x+y)%2=0 := by
              rw [hpow]
              simp [Nat.mul_mod]
            omega
          · have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat,
                  x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have hfactor : 2*(a-1)+8=2*a+6 := by omega
              have hsum' : x+y+1=2^n*(2*a+6) := by
                simpa [hfactor] using hpow
              have hcost' : 2*k+a+7+3*n=x+2*y := by
                rw [hfactor] at hcost
                omega
              have hnodd : n%2=1 := by omega
              have hnle : n≤1 := by
                by_cases hn2 : 2≤n
                · have hpowdiv : 2^2∣2^n := Nat.pow_dvd_pow 2 hn2
                  have ha3even : (a+3)%2=0 := by omega
                  have ha3div : 2∣a+3 :=
                    Nat.dvd_iff_mod_eq_zero.mpr ha3even
                  rcases hpowdiv with ⟨p,hp⟩
                  rcases ha3div with ⟨q,hq⟩
                  have hfac : 2*a+6=4*q := by omega
                  have hdiv : 16∣x+y+1 := by
                    refine ⟨p*q,?_⟩
                    calc
                      x+y+1=2^n*(2*a+6) := hsum'
                      _=(2^2*p)*(4*q) := by rw [← hp,hfac]
                      _=16*(p*q) := by
                        calc
                          (2^2*p)*(4*q)=(4*4)*(p*q) := by
                            simp only [show (2:Nat)^2=4 by decide]
                            ac_rfl
                          _=16*(p*q) := by rw [show 4*4=16 by decide]
                  have hzero := Nat.mod_eq_zero_of_dvd hdiv
                  omega
                · omega
              have hn : n=1 := by omega
              subst n
              have hA : a=AbxQ q := by
                dsimp [AbxQ,x,y,RxQ,RyQ]
                omega
              have hK : k=AbyQ q := by
                dsimp [AbyQ,x,y,RxQ,RyQ]
                omega
              right
              exact ⟨hA,hK⟩

def P1x (m : Nat) : Nat := 45806829964+96004895280*m
def P1y (m : Nat) : Nat := 30889617616+64740443880*m
def P1Dx (m : Nat) : Nat := 76696447578+160745339160*m
def P1Dy (m : Nat) : Nat := 15444808807+32370221940*m

/-- Every R(q), q=3 mod 8, is unreachable. The direct parent is
reduced through the odd/odd low-value inverse and the even-right
inverse; the bounce parent has odd/odd sum 2 mod 4. -/
theorem R_unreachable_q3 (q : Nat) (hq : q%8=3) :
    ¬ RunReach (RxQ q) (RyQ q) := by
  intro hR
  have hx : 5<RxQ q := by dsimp [RxQ]; omega
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent3Root32HighStopA4Core.run_parent_of_left_gt5
      (RxQ q) (RyQ q) hx hR
  rcases R_parent_fan_q3 q a k hq hstep with hdirect | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    have hRprime : RunReach (RpxQ q) (RpyQ q) := by
      simpa only [ha,hk] using hprev
    have hRfacts :
        5<RpxQ q ∧ RpxQ q%2=1 ∧ RpyQ q%2=1 ∧
        5≤RpyQ q ∧ (RpxQ q+RpyQ q)%4=0 ∧
        (RpxQ q+RpyQ q)%16≠0 ∧ 24≤RpxQ q+RpyQ q := by
      dsimp [RpxQ,RpyQ]
      omega
    have hRprimeC := toCReach (RpxQ q) (RpyQ q) hRprime
    have hP1C := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (RpxQ q) (RpyQ q) hRfacts.2.1 hRfacts.2.2.1
      hRfacts.2.2.2.1 hRfacts.2.2.2.2.1
      hRfacts.2.2.2.2.2.1 hRfacts.2.2.2.2.2.2).mp hRprimeC
    let m := q/8
    have hqEq : q=8*m+3 := by dsimp [m]; omega
    have hP1x :
        (RpxQ q+RpyQ q-4)/2=P1x m := by
      dsimp [P1x,RpxQ,RpyQ,m]
      rw [hqEq]
      omega
    have hP1y :
        (RpxQ q+3*RpyQ q-10)/4=P1y m := by
      dsimp [P1y,RpxQ,RpyQ,m]
      rw [hqEq]
      omega
    have hP1 : RunReach (P1x m) (P1y m) := by
      apply ofCReach (P1x m) (P1y m)
      simpa [BB6.Agent3.CReach,hP1x,hP1y] using hP1C
    have hP1facts :
        5<P1x m ∧ 6≤P1y m ∧ P1y m%2=0 ∧
        (P1x m+P1y m)%8≠0 ∧ (P1x m+P1y m)%8≠7 := by
      dsimp [P1x,P1y]
      omega
    have hP1C' := toCReach (P1x m) (P1y m) hP1
    have hP1D_C := (BB6.Agent46.six_even_right_blank_reach_iff
      (P1x m) (P1y m) hP1facts.2.1 hP1facts.2.2.1
      hP1facts.2.2.2.1 hP1facts.2.2.2.2).mp hP1C'
    have hP1Dx : P1x m+P1y m-2=P1Dx m := by
      dsimp [P1x,P1y,P1Dx]
      omega
    have hP1Dy : (P1y m-2)/2=P1Dy m := by
      dsimp [P1y,P1Dy]
      omega
    have hP1D : RunReach (P1Dx m) (P1Dy m) := by
      apply ofCReach (P1Dx m) (P1Dy m)
      simpa [BB6.Agent3.CReach,hP1Dx,hP1Dy] using hP1D_C
    have hP1Dfacts :
        5<P1Dx m ∧ 5≤P1Dy m ∧ P1Dy m%2=1 ∧
        (P1Dx m+P1Dy m)%4=1 := by
      dsimp [P1Dx,P1Dy]
      omega
    exact (BB6.Agent3Root32HighStopA4Core.run_no_odd_sum_one
      (P1Dx m) (P1Dy m) hP1Dfacts.1 hP1Dfacts.2.1
      hP1Dfacts.2.2.1 hP1Dfacts.2.2.2) hP1D
  · rcases hbounce with ⟨ha,hk⟩
    have hA : RunReach (AbxQ q) (AbyQ q) := by
      simpa only [ha,hk] using hprev
    have hAfacts :
        5<AbxQ q ∧ 5≤AbyQ q ∧ AbyQ q%2=1 ∧
        (AbxQ q+AbyQ q)%4=2 := by
      dsimp [AbxQ,AbyQ]
      omega
    exact (BB6.Agent3Root32HighStopA4Core.run_no_odd_sum_two
      (AbxQ q) (AbyQ q) hAfacts.1 hAfacts.2.1
      hAfacts.2.2.1 hAfacts.2.2.2) hA

/-- The E7 state is unreachable on the t=15 (mod 32) cylinder,
because its direct predecessor reduces to R(q), q=3 (mod 8). -/
theorem e7_unreachable_t15_mod32 (t : Nat) (ht : t%32=15) :
    ¬ BB6.Agent3Root32HighStopR10592Core.RunReach
      (BB6.Agent3Root32HighStopR10592Core.e7State t).1
      (BB6.Agent3Root32HighStopR10592Core.e7State t).2 := by
  open BB6.Agent3Root32HighStopR10592Core
  let q := t/4
  have hgood : goodEvenEven (e7State t) := by
    simp [goodEvenEven,e7State] <;> omega
  intro hE7
  have hP : directParent (e7State t)=pState t := by
    apply Prod.ext
    · dsimp [directParent,e7State,pState]
      omega
    · dsimp [directParent,e7State,pState]
      omega
  have hPReach : RunReach (pState t).1 (pState t).2 := by
    simpa only [hP] using even_even_direct_parent_reach
      (e7State t) hgood hE7
  have hPx : (pState t).1%2=0 := by dsimp [pState]; omega
  have hPy : (pState t).2%2=1 := by dsimp [pState]; omega
  have hPy5 : 5≤(pState t).2 := by dsimp [pState]; omega
  have hPmod : ((pState t).1+(pState t).2+1)%8=4 := by
    dsimp [pState]
    omega
  have hpa : ((pState t).1+(pState t).2-5)/2=(rState t).1 := by
    dsimp [pState,rState]
    omega
  have hpk : ((pState t).1+3*(pState t).2-9)/4=(rState t).2 := by
    dsimp [pState,rState]
    omega
  have hiff := BB6.Agent3.evenodd_four_blank_reach_iff
    (pState t).1 (pState t).2 hPx hPy hPy5 hPmod
  have hRReach : RunReach (rState t).1 (rState t).2 := by
    simpa [RunReach,BB6.Agent3Root32HighStopIntegrated.RunReach,hpa,hpk]
      using hiff.mp hPReach
  have ht4 : t=4*q+3 := by dsimp [q]; omega
  have hq : q%8=3 := by dsimp [q]; omega
  have hRx : (rState t).1=RxQ q := by
    rw [ht4]
    dsimp [rState,RxQ]
    omega
  have hRy : (rState t).2=RyQ q := by
    rw [ht4]
    dsimp [rState,RyQ]
    omega
  have hRReachQ : RunReach (RxQ q) (RyQ q) := by
    simpa only [hRx,hRy] using hRReach
  have hRReachQA4 : BB6.Agent3Root32HighStopA4Core.RunReach
      (RxQ q) (RyQ q) := by
    simpa [RunReach,BB6.Agent3Root32HighStopIntegrated.RunReach,
      BB6.Agent3Root32HighStopA4Core.RunReach] using hRReachQ
  exact R_unreachable_q3 q hq hRReachQA4

/-- The D0E residual is unreachable whenever t=15 (mod 32). -/
theorem d0e_unreachable_t15_mod32 (t : Nat) (ht : t%32=15) :
    ¬ BB6.Agent3Root32HighStopR10592Core.RunReach
      (BB6.Agent3Root32HighStopR10592Core.d0e0 (1802+6720*t)).1
      (BB6.Agent3Root32HighStopR10592Core.d0e0 (1802+6720*t)).2 := by
  open BB6.Agent3Root32HighStopR10592Core
  intro hD0
  have hD7 := d0e0_reach_forces_d0e7 t hD0
  rcases d0e7_reach_fork t hD7 with hD8 | hE7
  · exact d0e8_unreachable t hD8
  · exact e7_unreachable_t15_mod32 t ht hE7

#print axioms R_parent_fan_q3
#print axioms R_unreachable_q3
#print axioms e7_unreachable_t15_mod32
#print axioms d0e_unreachable_t15_mod32

end BB6.Agent6RRoot32Q3Closure

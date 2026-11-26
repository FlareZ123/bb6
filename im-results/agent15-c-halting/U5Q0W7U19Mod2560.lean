import U5Q0W7ParentFan
import OddOddLowVal
import SectionEvenOddSum3Inverse
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

/-!
A fifth exact-source q=1 exclusion on the U5 w=7, z=2 (mod 4) branch.
For u=339+2560*v, the forced source ancestry is:
odd/odd low-value -> even/odd sum-three -> even-right six -> odd/odd
low-value -> odd-right sum-one blank-image obstruction.
This is a new root-compatible cylinder, distinct from the four earlier
q=1 sublifts.
-/

namespace BB6.Agent15U5W7U19Mod2560
open BB6.Agent46

/-- The q=1 parent is blank-unreachable for u=339+2560*v. -/
theorem w7_z2_q1_parent_unreachable_u339mod2560 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (2439151+18385920*v) (13386813+100907520*v) := by
  let Ax : Nat := 2439151+18385920*v
  let Ay : Nat := 13386813+100907520*v
  let Bx : Nat := 7912980+59646720*v
  let By : Nat := 10649895+80277120*v
  let Cx : Nat := 9281435+69961920*v
  let Cy : Nat := 9965664+75119520*v
  let Dx : Nat := 19247097+145081440*v
  let Dy : Nat := 4982831+37559760*v
  let Fx : Nat := 12114962+91320600*v
  let Fy : Nat := 8548895+64440180*v
  have hAx : 5<Ax := by dsimp [Ax]; omega
  have hAxOdd : Ax%2=1 := by dsimp [Ax]; omega
  have hAyOdd : Ay%2=1 := by dsimp [Ay]; omega
  have hAy5 : 5≤Ay := by dsimp [Ay]; omega
  have hAsum4 : (Ax+Ay)%4=0 := by dsimp [Ax,Ay]; omega
  have hAsum16 : (Ax+Ay)%16≠0 := by dsimp [Ax,Ay]; omega
  have hAsize : 24≤Ax+Ay := by dsimp [Ax,Ay]; omega
  intro hA
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 Ax Ay hAx hA
  have hAparent :=
    (BB6.Agent3.oddodd_lowval_parent_iff a k Ax Ay
      hAxOdd hAyOdd hAy5 hAsum4 hAsum16 hAsize).mp hstep
  rcases hAparent with ⟨hsumA,hcostA⟩
  have haB : a=Bx := by dsimp [Ax,Ay,Bx] at hsumA ⊢; omega
  have hkB : k=By := by dsimp [Ax,Ay,By] at hcostA ⊢; omega
  have hB : BB6.Agent3.CReach Bx By := by
    rw [haB,hkB] at hprev
    exact hprev
  have hBxEven : Bx%2=0 := by dsimp [Bx]; omega
  have hByOdd : By%2=1 := by dsimp [By]; omega
  have hBy5 : 5≤By := by dsimp [By]; omega
  have hBsum : (Bx+By)%8=3 := by dsimp [Bx,By]; omega
  obtain ⟨a2,k2,hprev2,hstep2⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      Bx By (by dsimp [Bx]; omega) hB
  have hBparent :=
    BB6.Agent46SourceInverse.section_evenodd_sum3_inverse
      a2 k2 Bx By hBy5 hByOdd hBsum hstep2
  rcases hBparent with ⟨hsumB,hcostB⟩
  have haC : a2=Cx := by dsimp [Bx,By,Cx] at hsumB ⊢; omega
  have hkC : k2=Cy := by dsimp [By,Cy] at hcostB ⊢; omega
  have hC : BB6.Agent3.CReach Cx Cy := by
    rw [haC,hkC] at hprev2
    exact hprev2
  have hCy6 : 6≤Cy := by dsimp [Cy]; omega
  have hCyEven : Cy%2=0 := by dsimp [Cy]; omega
  have hCsum : (Cx+Cy)%8=3 := by dsimp [Cx,Cy]; omega
  have hD : BB6.Agent3.CReach Dx Dy := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      Cx Cy hCy6 hCyEven (by omega) (by omega)).mp hC
    have hx : Cx+Cy-2=Dx := by dsimp [Cx,Cy,Dx]; omega
    have hy : (Cy-2)/2=Dy := by dsimp [Cy,Dy]; omega
    simpa only [hx,hy] using hp
  have hDx : 5<Dx := by dsimp [Dx]; omega
  have hDxOdd : Dx%2=1 := by dsimp [Dx]; omega
  have hDyOdd : Dy%2=1 := by dsimp [Dy]; omega
  have hDy5 : 5≤Dy := by dsimp [Dy]; omega
  have hDsum4 : (Dx+Dy)%4=0 := by dsimp [Dx,Dy]; omega
  have hDsum16 : (Dx+Dy)%16≠0 := by dsimp [Dx,Dy]; omega
  have hDsize : 24≤Dx+Dy := by dsimp [Dx,Dy]; omega
  obtain ⟨a4,k4,hprev4,hstep4⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      Dx Dy hDx hD
  have hDparent :=
    (BB6.Agent3.oddodd_lowval_parent_iff a4 k4 Dx Dy
      hDxOdd hDyOdd hDy5 hDsum4 hDsum16 hDsize).mp hstep4
  rcases hDparent with ⟨hsumD,hcostD⟩
  have haF : a4=Fx := by dsimp [Dx,Dy,Fx] at hsumD ⊢; omega
  have hkF : k4=Fy := by dsimp [Dx,Dy,Fy] at hcostD ⊢; omega
  have hF : BB6.Agent3.CReach Fx Fy := by
    rw [haF,hkF] at hprev4
    exact hprev4
  have hFx5 : 5<Fx := by dsimp [Fx]; omega
  have hFy5 : 5≤Fy := by dsimp [Fy]; omega
  have hFyOdd : Fy%2=1 := by dsimp [Fy]; omega
  have hFsum : (Fx+Fy)%4=1 := by dsimp [Fx,Fy]; omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    Fx Fy hFx5 hFy5 hFyOdd hFsum hF

/-- The original q=0 U5 w=7 target is blank-unreachable on
    u=339+2560*v. -/
theorem w7_q0_target_unreachable_u339mod2560 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(339+2560*v)) (17719+28560*(339+2560*v)) := by
  let u : Nat := 339+2560*v
  let x : Nat := 17928+28896*u
  let y : Nat := 17719+28560*u
  let W : Nat := 2228+3591*u
  let X2 : Nat := 53366+86016*u
  change ¬ BB6.Agent3.CReach x y
  intro hP
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      x y (by dsimp [x]; omega) hP
  have hpre : BB6.Agent46.sectionPreimageAll a k x y :=
    (BB6.Agent46.section_preimage_all_iff a k x y).mp hstep
  obtain ⟨n,hn,hscale,hcost⟩ :=
    BB6.Agent15U5W7Source.w7_z2_parent_fan u a k hpre
  have hWodd : W%2=1 := by dsimp [W,u]; omega
  have hnle : n≤2 := by
    by_cases hsmall : n≤2
    · exact hsmall
    · have hn4 : 4≤n := by omega
      have hpow : 32∣2^(n+1) := by
        change 2^5∣2^(n+1)
        exact Nat.pow_dvd_pow 2 (by omega)
      have hdiv : 32∣2^(n+1)*(a+3) := by
        rcases hpow with ⟨q,hq⟩
        have hq' : 2^(n+1)=32*q := by simpa using hq
        refine ⟨q*(a+3),?_⟩
        rw [hq']
        simp [Nat.mul_assoc]
      have hmod : (2^(n+1)*(a+3))%32=0 :=
        Nat.mod_eq_zero_of_dvd hdiv
      rw [hscale] at hmod
      have hmodW : (16*W)%32=16 := by dsimp [W,u]; omega
      omega
  have hnCases : n=0 ∨ n=2 := by omega
  rcases hnCases with hn0 | hn2
  · subst n
    have ha : a=8*W-3 := by
      have htmp : 2*(a+3)=16*W := by simpa using hscale
      omega
    have hk : k=17769+28644*u := by
      rw [ha] at hcost
      dsimp [W,X2] at hcost
      omega
    have hbad := BB6.Agent15U5W7Source.w7_z2_q0_parent_unreachable u
    exact hbad (by simpa [W,ha,hk] using hprev)
  · subst n
    have htmp : 8*(a+3)=16*W := by simpa using hscale
    have ha : a=2*W-3 := by omega
    have hk : k=24450+39417*u := by
      rw [ha] at hcost
      dsimp [W,X2] at hcost
      omega
    have hax : 2*W-3=2439151+18385920*v := by dsimp [W,u]; omega
    have hay : 24450+39417*u=13386813+100907520*v := by dsimp [u]; omega
    have hbad :=
      w7_z2_q1_parent_unreachable_u339mod2560 v
    rw [ha,hk] at hprev
    exact hbad (by simpa only [hax,hay] using hprev)

#print axioms w7_z2_q1_parent_unreachable_u339mod2560
#print axioms w7_q0_target_unreachable_u339mod2560

end BB6.Agent15U5W7U19Mod2560

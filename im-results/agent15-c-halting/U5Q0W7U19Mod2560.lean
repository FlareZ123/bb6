import U5Q0W7ParentFan
import OddOddLowVal
import SectionEvenOddSum3Inverse
import EvenRightSixOrbit
import HighSumTwo
import HighEvenRightSum7Source
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


/-- A second new q=1 exclusion, on u=499+1280*v. Its forced
    ancestry is odd/odd low-value, even/odd sum-three, then two
    exact even-right inverses, ending at an odd-right sum-two state. -/
theorem w7_z2_q1_parent_unreachable_u499mod1280 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (3588271+9192960*v) (19693533+50453760*v) := by
  let Ax : Nat := 3588271+9192960*v
  let Ay : Nat := 19693533+50453760*v
  let Bx : Nat := 11640900+29823360*v
  let By : Nat := 15667215+40138560*v
  let Cx : Nat := 13654055+34980960*v
  let Cy : Nat := 14660634+37559760*v
  let Dx : Nat := 28314687+72540720*v
  let Dy : Nat := 7330316+18779880*v
  let Ex : Nat := 35645001+91320600*v
  let Ey : Nat := 3665157+9389940*v
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
  have hCsum : (Cx+Cy)%8=1 := by dsimp [Cx,Cy]; omega
  have hD : BB6.Agent3.CReach Dx Dy := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      Cx Cy hCy6 hCyEven (by omega) (by omega)).mp hC
    have hx : Cx+Cy-2=Dx := by dsimp [Cx,Cy,Dx]; omega
    have hy : (Cy-2)/2=Dy := by dsimp [Cy,Dy]; omega
    simpa only [hx,hy] using hp
  have hDy6 : 6≤Dy := by dsimp [Dy]; omega
  have hDyEven : Dy%2=0 := by dsimp [Dy]; omega
  have hDsum : (Dx+Dy)%8=3 := by dsimp [Dx,Dy]; omega
  have hE : BB6.Agent3.CReach Ex Ey := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      Dx Dy hDy6 hDyEven (by omega) (by omega)).mp hD
    have hx : Dx+Dy-2=Ex := by dsimp [Dx,Dy,Ex]; omega
    have hy : (Dy-2)/2=Ey := by dsimp [Dy,Ey]; omega
    simpa only [hx,hy] using hp
  have hEy5 : 5≤Ey := by dsimp [Ey]; omega
  have hEyOdd : Ey%2=1 := by dsimp [Ey]; omega
  have hEsum : (Ex+Ey)%4=2 := by dsimp [Ex,Ey]; omega
  exact BB6.Agent11High.blank_no_odd_sum_two
    Ex Ey hEy5 hEyOdd hEsum hE

/-- The original q=0 U5 w=7 target is blank-unreachable on
    u=499+1280*v. -/
theorem w7_q0_target_unreachable_u499mod1280 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(499+1280*v)) (17719+28560*(499+1280*v)) := by
  let u : Nat := 499+1280*v
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
    have hax : 2*W-3=3588271+9192960*v := by dsimp [W,u]; omega
    have hay : 24450+39417*u=19693533+50453760*v := by dsimp [u]; omega
    have hbad := w7_z2_q1_parent_unreachable_u499mod1280 v
    rw [ha,hk] at hprev
    exact hbad (by simpa only [hax,hay] using hprev)

#print axioms w7_z2_q1_parent_unreachable_u499mod1280
#print axioms w7_q0_target_unreachable_u499mod1280


/-- A third disjoint q=1 exclusion, on u=3379+5120*v. After the
    odd/odd and even/odd inverses, four exact even-right inverses force
    an odd/odd sum-two state. -/
theorem w7_z2_q1_parent_unreachable_u3379mod5120 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (24272431+36771840*v) (133214493+201815040*v) := by
  let Ax : Nat := 24272431+36771840*v
  let Ay : Nat := 133214493+201815040*v
  let Bx : Nat := 78743460+119293440*v
  let By : Nat := 105978975+160554240*v
  let Cx : Nat := 92361215+139923840*v
  let Cy : Nat := 99170094+150239040*v
  let D1x : Nat := 191531307+290162880*v
  let D1y : Nat := 49585046+75119520*v
  let D2x : Nat := 241116351+365282400*v
  let D2y : Nat := 24792522+37559760*v
  let D3x : Nat := 265908871+402842160*v
  let D3y : Nat := 12396260+18779880*v
  let Fx : Nat := 278305129+421622040*v
  let Fy : Nat := 6198129+9389940*v
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
  have hCsum : (Cx+Cy)%8=5 := by dsimp [Cx,Cy]; omega
  have hD1 : BB6.Agent3.CReach D1x D1y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      Cx Cy hCy6 hCyEven (by omega) (by omega)).mp hC
    have hx : Cx+Cy-2=D1x := by dsimp [Cx,Cy,D1x]; omega
    have hy : (Cy-2)/2=D1y := by dsimp [Cy,D1y]; omega
    simpa only [hx,hy] using hp
  have hD1y6 : 6≤D1y := by dsimp [D1y]; omega
  have hD1yEven : D1y%2=0 := by dsimp [D1y]; omega
  have hD1sum : (D1x+D1y)%8=1 := by dsimp [D1x,D1y]; omega
  have hD2 : BB6.Agent3.CReach D2x D2y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D1x D1y hD1y6 hD1yEven (by omega) (by omega)).mp hD1
    have hx : D1x+D1y-2=D2x := by dsimp [D1x,D1y,D2x]; omega
    have hy : (D1y-2)/2=D2y := by dsimp [D1y,D2y]; omega
    simpa only [hx,hy] using hp
  have hD2y6 : 6≤D2y := by dsimp [D2y]; omega
  have hD2yEven : D2y%2=0 := by dsimp [D2y]; omega
  have hD2sum : (D2x+D2y)%8=1 := by dsimp [D2x,D2y]; omega
  have hD3 : BB6.Agent3.CReach D3x D3y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D2x D2y hD2y6 hD2yEven (by omega) (by omega)).mp hD2
    have hx : D2x+D2y-2=D3x := by dsimp [D2x,D2y,D3x]; omega
    have hy : (D2y-2)/2=D3y := by dsimp [D2y,D3y]; omega
    simpa only [hx,hy] using hp
  have hD3y6 : 6≤D3y := by dsimp [D3y]; omega
  have hD3yEven : D3y%2=0 := by dsimp [D3y]; omega
  have hD3sum : (D3x+D3y)%8=3 := by dsimp [D3x,D3y]; omega
  have hF : BB6.Agent3.CReach Fx Fy := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D3x D3y hD3y6 hD3yEven (by omega) (by omega)).mp hD3
    have hx : D3x+D3y-2=Fx := by dsimp [D3x,D3y,Fx]; omega
    have hy : (D3y-2)/2=Fy := by dsimp [D3y,Fy]; omega
    simpa only [hx,hy] using hp
  have hFy5 : 5≤Fy := by dsimp [Fy]; omega
  have hFyOdd : Fy%2=1 := by dsimp [Fy]; omega
  have hFsum : (Fx+Fy)%4=2 := by dsimp [Fx,Fy]; omega
  exact BB6.Agent11High.blank_no_odd_sum_two
    Fx Fy hFy5 hFyOdd hFsum hF

/-- The original q=0 U5 w=7 target is blank-unreachable on
    u=3379+5120*v. -/
theorem w7_q0_target_unreachable_u3379mod5120 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(3379+5120*v)) (17719+28560*(3379+5120*v)) := by
  let u : Nat := 3379+5120*v
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
    have hax : 2*W-3=24272431+36771840*v := by dsimp [W,u]; omega
    have hay : 24450+39417*u=133214493+201815040*v := by dsimp [u]; omega
    have hbad := w7_z2_q1_parent_unreachable_u3379mod5120 v
    rw [ha,hk] at hprev
    exact hbad (by simpa only [hax,hay] using hprev)

#print axioms w7_z2_q1_parent_unreachable_u3379mod5120
#print axioms w7_q0_target_unreachable_u3379mod5120


/-- A fourth new q=1 exclusion, on u=2739+10240*v. Three exact
    even-right inverses followed by the odd/odd low-value inverse reach
    an odd-right sum-one state. -/
theorem w7_z2_q1_parent_unreachable_u2739mod10240 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (19675951+73543680*v) (107987613+403630080*v) := by
  let Ax : Nat := 19675951+73543680*v
  let Ay : Nat := 107987613+403630080*v
  let Bx : Nat := 63831780+238586880*v
  let By : Nat := 85909695+321108480*v
  let Cx : Nat := 74870735+279847680*v
  let Cy : Nat := 80390214+300478080*v
  let D1x : Nat := 155260947+580325760*v
  let D1y : Nat := 40195106+150239040*v
  let D2x : Nat := 195456051+730564800*v
  let D2y : Nat := 20097552+75119520*v
  let D3x : Nat := 215553601+805684320*v
  let D3y : Nat := 10048775+37559760*v
  let Fx : Nat := 112801186+421622040*v
  let Fy : Nat := 61424979+229590900*v
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
  have hCsum : (Cx+Cy)%8=5 := by dsimp [Cx,Cy]; omega
  have hD1 : BB6.Agent3.CReach D1x D1y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      Cx Cy hCy6 hCyEven (by omega) (by omega)).mp hC
    have hx : Cx+Cy-2=D1x := by dsimp [Cx,Cy,D1x]; omega
    have hy : (Cy-2)/2=D1y := by dsimp [Cy,D1y]; omega
    simpa only [hx,hy] using hp
  have hD1y6 : 6≤D1y := by dsimp [D1y]; omega
  have hD1yEven : D1y%2=0 := by dsimp [D1y]; omega
  have hD1sum : (D1x+D1y)%8=5 := by dsimp [D1x,D1y]; omega
  have hD2 : BB6.Agent3.CReach D2x D2y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D1x D1y hD1y6 hD1yEven (by omega) (by omega)).mp hD1
    have hx : D1x+D1y-2=D2x := by dsimp [D1x,D1y,D2x]; omega
    have hy : (D1y-2)/2=D2y := by dsimp [D1y,D2y]; omega
    simpa only [hx,hy] using hp
  have hD2y6 : 6≤D2y := by dsimp [D2y]; omega
  have hD2yEven : D2y%2=0 := by dsimp [D2y]; omega
  have hD2sum : (D2x+D2y)%8=3 := by dsimp [D2x,D2y]; omega
  have hD3 : BB6.Agent3.CReach D3x D3y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D2x D2y hD2y6 hD2yEven (by omega) (by omega)).mp hD2
    have hx : D2x+D2y-2=D3x := by dsimp [D2x,D2y,D3x]; omega
    have hy : (D2y-2)/2=D3y := by dsimp [D2y,D3y]; omega
    simpa only [hx,hy] using hp
  have hD3x : 5<D3x := by dsimp [D3x]; omega
  have hD3xOdd : D3x%2=1 := by dsimp [D3x]; omega
  have hD3yOdd : D3y%2=1 := by dsimp [D3y]; omega
  have hD3y5 : 5≤D3y := by dsimp [D3y]; omega
  have hD3sum4 : (D3x+D3y)%4=0 := by dsimp [D3x,D3y]; omega
  have hD3sum16 : (D3x+D3y)%16≠0 := by dsimp [D3x,D3y]; omega
  have hD3size : 24≤D3x+D3y := by dsimp [D3x,D3y]; omega
  obtain ⟨a4,k4,hprev4,hstep4⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      D3x D3y hD3x hD3
  have hD3parent :=
    (BB6.Agent3.oddodd_lowval_parent_iff a4 k4 D3x D3y
      hD3xOdd hD3yOdd hD3y5 hD3sum4 hD3sum16 hD3size).mp hstep4
  rcases hD3parent with ⟨hsumD3,hcostD3⟩
  have haF : a4=Fx := by dsimp [D3x,D3y,Fx] at hsumD3 ⊢; omega
  have hkF : k4=Fy := by dsimp [D3x,D3y,Fy] at hcostD3 ⊢; omega
  have hF : BB6.Agent3.CReach Fx Fy := by
    rw [haF,hkF] at hprev4
    exact hprev4
  have hFy5 : 5≤Fy := by dsimp [Fy]; omega
  have hFyOdd : Fy%2=1 := by dsimp [Fy]; omega
  have hFsum : (Fx+Fy)%4=1 := by dsimp [Fx,Fy]; omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    Fx Fy (by dsimp [Fx]; omega) hFy5 hFyOdd hFsum hF

/-- The original q=0 U5 w=7 target is blank-unreachable on
    u=2739+10240*v. -/
theorem w7_q0_target_unreachable_u2739mod10240 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(2739+10240*v)) (17719+28560*(2739+10240*v)) := by
  let u : Nat := 2739+10240*v
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
    have hax : 2*W-3=19675951+73543680*v := by dsimp [W,u]; omega
    have hay : 24450+39417*u=107987613+403630080*v := by dsimp [u]; omega
    have hbad := w7_z2_q1_parent_unreachable_u2739mod10240 v
    rw [ha,hk] at hprev
    exact hbad (by simpa only [hax,hay] using hprev)

/-- A fifth new q=1 exclusion, on u=9939+10240*v. It alternates
    even-right six, odd/odd low-value, then two more even-right six
    inverses, ending at an odd-right sum-one state. -/
theorem w7_z2_q1_parent_unreachable_u9939mod10240 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (71386351+73543680*v) (391790013+403630080*v) := by
  let Ax : Nat := 71386351+73543680*v
  let Ay : Nat := 391790013+403630080*v
  let Bx : Nat := 231588180+238586880*v
  let By : Nat := 311689095+321108480*v
  let Cx : Nat := 271638635+279847680*v
  let Cy : Nat := 291663864+300478080*v
  let D1x : Nat := 563302497+580325760*v
  let D1y : Nat := 145831931+150239040*v
  let D2x : Nat := 354567212+365282400*v
  let D2y : Nat := 250199570+257760720*v
  let D3x : Nat := 604766780+623043120*v
  let D3y : Nat := 125099784+128880360*v
  let Fx : Nat := 729866562+751923480*v
  let Fy : Nat := 62549891+64440180*v
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
  have hD1 : BB6.Agent3.CReach D1x D1y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      Cx Cy hCy6 hCyEven (by omega) (by omega)).mp hC
    have hx : Cx+Cy-2=D1x := by dsimp [Cx,Cy,D1x]; omega
    have hy : (Cy-2)/2=D1y := by dsimp [Cy,D1y]; omega
    simpa only [hx,hy] using hp
  have hD1x : 5<D1x := by dsimp [D1x]; omega
  have hD1xOdd : D1x%2=1 := by dsimp [D1x]; omega
  have hD1yOdd : D1y%2=1 := by dsimp [D1y]; omega
  have hD1y5 : 5≤D1y := by dsimp [D1y]; omega
  have hD1sum4 : (D1x+D1y)%4=0 := by dsimp [D1x,D1y]; omega
  have hD1sum16 : (D1x+D1y)%16≠0 := by dsimp [D1x,D1y]; omega
  have hD1size : 24≤D1x+D1y := by dsimp [D1x,D1y]; omega
  obtain ⟨a3,k3,hprev3,hstep3⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      D1x D1y hD1x hD1
  have hD1parent :=
    (BB6.Agent3.oddodd_lowval_parent_iff a3 k3 D1x D1y
      hD1xOdd hD1yOdd hD1y5 hD1sum4 hD1sum16 hD1size).mp hstep3
  rcases hD1parent with ⟨hsumD1,hcostD1⟩
  have haD2 : a3=D2x := by dsimp [D1x,D1y,D2x] at hsumD1 ⊢; omega
  have hkD2 : k3=D2y := by dsimp [D1x,D1y,D2y] at hcostD1 ⊢; omega
  have hD2 : BB6.Agent3.CReach D2x D2y := by
    rw [haD2,hkD2] at hprev3
    exact hprev3
  have hD2y6 : 6≤D2y := by dsimp [D2y]; omega
  have hD2yEven : D2y%2=0 := by dsimp [D2y]; omega
  have hD2sum : (D2x+D2y)%8=6 := by dsimp [D2x,D2y]; omega
  have hD3 : BB6.Agent3.CReach D3x D3y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D2x D2y hD2y6 hD2yEven (by omega) (by omega)).mp hD2
    have hx : D2x+D2y-2=D3x := by dsimp [D2x,D2y,D3x]; omega
    have hy : (D2y-2)/2=D3y := by dsimp [D2y,D3y]; omega
    simpa only [hx,hy] using hp
  have hD3y6 : 6≤D3y := by dsimp [D3y]; omega
  have hD3yEven : D3y%2=0 := by dsimp [D3y]; omega
  have hD3sum : (D3x+D3y)%8=4 := by dsimp [D3x,D3y]; omega
  have hF : BB6.Agent3.CReach Fx Fy := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D3x D3y hD3y6 hD3yEven (by omega) (by omega)).mp hD3
    have hx : D3x+D3y-2=Fx := by dsimp [D3x,D3y,Fx]; omega
    have hy : (D3y-2)/2=Fy := by dsimp [D3y,Fy]; omega
    simpa only [hx,hy] using hp
  have hFy5 : 5≤Fy := by dsimp [Fy]; omega
  have hFyOdd : Fy%2=1 := by dsimp [Fy]; omega
  have hFsum : (Fx+Fy)%4=1 := by dsimp [Fx,Fy]; omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    Fx Fy (by dsimp [Fx]; omega) hFy5 hFyOdd hFsum hF

/-- The original q=0 U5 w=7 target is blank-unreachable on
    u=9939+10240*v. -/
theorem w7_q0_target_unreachable_u9939mod10240 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(9939+10240*v)) (17719+28560*(9939+10240*v)) := by
  let u : Nat := 9939+10240*v
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
    have hax : 2*W-3=71386351+73543680*v := by dsimp [W,u]; omega
    have hay : 24450+39417*u=391790013+403630080*v := by dsimp [u]; omega
    have hbad := w7_z2_q1_parent_unreachable_u9939mod10240 v
    rw [ha,hk] at hprev
    exact hbad (by simpa only [hax,hay] using hprev)

#print axioms w7_z2_q1_parent_unreachable_u2739mod10240
#print axioms w7_q0_target_unreachable_u2739mod10240
#print axioms w7_z2_q1_parent_unreachable_u9939mod10240
#print axioms w7_q0_target_unreachable_u9939mod10240


/-- Generic lift from an odd-W q=1 parent exclusion to its q=0 target.
    This factors the exact even-depth parent fan for later cylinders. -/
theorem w7_q0_target_unreachable_of_q1 (u : Nat) (huodd : u%2=1)
    (hq1 : ¬ BB6.Agent3.CReach
      (2*(2228+3591*u)-3) (24450+39417*u)) :
    ¬ BB6.Agent3.CReach
      (17928+28896*u) (17719+28560*u) := by
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
  have hWodd : W%2=1 := by dsimp [W]; omega
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
      have hmodW : (16*W)%32=16 := by dsimp [W]; omega
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
    have hbad : ¬ BB6.Agent3.CReach (2*W-3) (24450+39417*u) := by
      simpa [W] using hq1
    exact hbad (by simpa [ha,hk] using hprev)

/-- A sixth new q=1 exclusion, on u=16339+20480*v. The chain is
    odd/odd low-value, even/odd sum-three, even-right six,
    odd/odd low-value, even-right six, even/odd sum-three. -/
theorem w7_z2_q1_parent_unreachable_u16339mod20480 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (117351151+147087360*v) (644058813+807260160*v) := by
  let Ax : Nat := 117351151+147087360*v
  let Ay : Nat := 644058813+807260160*v
  let Bx : Nat := 380704980+477173760*v
  let By : Nat := 512381895+642216960*v
  let Cx : Nat := 446543435+559695360*v
  let Cy : Nat := 479462664+600956160*v
  let D1x : Nat := 926006097+1160651520*v
  let D1y : Nat := 239731331+300478080*v
  let D2x : Nat := 582868712+730564800*v
  let D2y : Nat := 411300020+515521440*v
  let D3x : Nat := 994168730+1246086240*v
  let D3y : Nat := 205650009+257760720*v
  let Fx : Nat := 599909367+751923480*v
  let Fy : Nat := 402779687+504842100*v
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
  have hD1 : BB6.Agent3.CReach D1x D1y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      Cx Cy hCy6 hCyEven (by omega) (by omega)).mp hC
    have hx : Cx+Cy-2=D1x := by dsimp [Cx,Cy,D1x]; omega
    have hy : (Cy-2)/2=D1y := by dsimp [Cy,D1y]; omega
    simpa only [hx,hy] using hp
  have hD1x : 5<D1x := by dsimp [D1x]; omega
  have hD1xOdd : D1x%2=1 := by dsimp [D1x]; omega
  have hD1yOdd : D1y%2=1 := by dsimp [D1y]; omega
  have hD1y5 : 5≤D1y := by dsimp [D1y]; omega
  have hD1sum4 : (D1x+D1y)%4=0 := by dsimp [D1x,D1y]; omega
  have hD1sum16 : (D1x+D1y)%16≠0 := by dsimp [D1x,D1y]; omega
  have hD1size : 24≤D1x+D1y := by dsimp [D1x,D1y]; omega
  obtain ⟨a3,k3,hprev3,hstep3⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      D1x D1y hD1x hD1
  have hD1parent :=
    (BB6.Agent3.oddodd_lowval_parent_iff a3 k3 D1x D1y
      hD1xOdd hD1yOdd hD1y5 hD1sum4 hD1sum16 hD1size).mp hstep3
  rcases hD1parent with ⟨hsumD1,hcostD1⟩
  have haD2 : a3=D2x := by dsimp [D1x,D1y,D2x] at hsumD1 ⊢; omega
  have hkD2 : k3=D2y := by dsimp [D1x,D1y,D2y] at hcostD1 ⊢; omega
  have hD2 : BB6.Agent3.CReach D2x D2y := by
    rw [haD2,hkD2] at hprev3
    exact hprev3
  have hD2y6 : 6≤D2y := by dsimp [D2y]; omega
  have hD2yEven : D2y%2=0 := by dsimp [D2y]; omega
  have hD2sum : (D2x+D2y)%8=4 := by dsimp [D2x,D2y]; omega
  have hD3 : BB6.Agent3.CReach D3x D3y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D2x D2y hD2y6 hD2yEven (by omega) (by omega)).mp hD2
    have hx : D2x+D2y-2=D3x := by dsimp [D2x,D2y,D3x]; omega
    have hy : (D2y-2)/2=D3y := by dsimp [D2y,D3y]; omega
    simpa only [hx,hy] using hp
  have hD3y5 : 5≤D3y := by dsimp [D3y]; omega
  have hD3yOdd : D3y%2=1 := by dsimp [D3y]; omega
  have hD3sum : (D3x+D3y)%8=3 := by dsimp [D3x,D3y]; omega
  obtain ⟨a4,k4,hprev4,hstep4⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      D3x D3y (by dsimp [D3x]; omega) hD3
  have hD3parent :=
    BB6.Agent46SourceInverse.section_evenodd_sum3_inverse
      a4 k4 D3x D3y hD3y5 hD3yOdd hD3sum hstep4
  rcases hD3parent with ⟨hsumD3,hcostD3⟩
  have haF : a4=Fx := by dsimp [D3x,D3y,Fx] at hsumD3 ⊢; omega
  have hkF : k4=Fy := by dsimp [D3y,Fy] at hcostD3 ⊢; omega
  have hF : BB6.Agent3.CReach Fx Fy := by
    rw [haF,hkF] at hprev4
    exact hprev4
  have hFy5 : 5≤Fy := by dsimp [Fy]; omega
  have hFyOdd : Fy%2=1 := by dsimp [Fy]; omega
  have hFsum : (Fx+Fy)%4=2 := by dsimp [Fx,Fy]; omega
  exact BB6.Agent11High.blank_no_odd_sum_two
    Fx Fy hFy5 hFyOdd hFsum hF

/-- The original q=0 target is excluded on u=16339+20480*v. -/
theorem w7_q0_target_unreachable_u16339mod20480 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(16339+20480*v)) (17719+28560*(16339+20480*v)) := by
  let u : Nat := 16339+20480*v
  have hq1 : ¬ BB6.Agent3.CReach
      (2*(2228+3591*u)-3) (24450+39417*u) := by
    intro h
    have hx : 2*(2228+3591*u)-3=117351151+147087360*v := by
      dsimp [u]
      omega
    have hy : 24450+39417*u=644058813+807260160*v := by
      dsimp [u]
      omega
    exact w7_z2_q1_parent_unreachable_u16339mod20480 v
      (by simpa only [hx,hy] using h)
  exact w7_q0_target_unreachable_of_q1 u (by dsimp [u]; omega) hq1

/-- A seventh new q=1 exclusion, on u=20019+20480*v. Six exact
    even-right inverses after the odd/odd and even/odd source inverses
    reach an odd-right sum-two state. -/
theorem w7_z2_q1_parent_unreachable_u20019mod20480 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (143780911+147087360*v) (789113373+807260160*v) := by
  let Ax : Nat := 143780911+147087360*v
  let Ay : Nat := 789113373+807260160*v
  let Bx : Nat := 466447140+477173760*v
  let By : Nat := 627780255+642216960*v
  let Cx : Nat := 547113695+559695360*v
  let Cy : Nat := 587446974+600956160*v
  let D1x : Nat := 1134560667+1160651520*v
  let D1y : Nat := 293723486+300478080*v
  let D2x : Nat := 1428284151+1461129600*v
  let D2y : Nat := 146861742+150239040*v
  let D3x : Nat := 1575145891+1611368640*v
  let D3y : Nat := 73430870+75119520*v
  let D4x : Nat := 1648576759+1686488160*v
  let D4y : Nat := 36715434+37559760*v
  let D5x : Nat := 1685292191+1724047920*v
  let D5y : Nat := 18357716+18779880*v
  let Fx : Nat := 1703649905+1742827800*v
  let Fy : Nat := 9178857+9389940*v
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
  have hCsum : (Cx+Cy)%8=5 := by dsimp [Cx,Cy]; omega
  have hD1 : BB6.Agent3.CReach D1x D1y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      Cx Cy hCy6 hCyEven (by omega) (by omega)).mp hC
    have hx : Cx+Cy-2=D1x := by dsimp [Cx,Cy,D1x]; omega
    have hy : (Cy-2)/2=D1y := by dsimp [Cy,D1y]; omega
    simpa only [hx,hy] using hp
  have hD1y6 : 6≤D1y := by dsimp [D1y]; omega
  have hD1yEven : D1y%2=0 := by dsimp [D1y]; omega
  have hD1sum : (D1x+D1y)%8=1 := by dsimp [D1x,D1y]; omega
  have hD2 : BB6.Agent3.CReach D2x D2y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D1x D1y hD1y6 hD1yEven (by omega) (by omega)).mp hD1
    have hx : D1x+D1y-2=D2x := by dsimp [D1x,D1y,D2x]; omega
    have hy : (D1y-2)/2=D2y := by dsimp [D1y,D2y]; omega
    simpa only [hx,hy] using hp
  have hD2y6 : 6≤D2y := by dsimp [D2y]; omega
  have hD2yEven : D2y%2=0 := by dsimp [D2y]; omega
  have hD2sum : (D2x+D2y)%8=5 := by dsimp [D2x,D2y]; omega
  have hD3 : BB6.Agent3.CReach D3x D3y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D2x D2y hD2y6 hD2yEven (by omega) (by omega)).mp hD2
    have hx : D2x+D2y-2=D3x := by dsimp [D2x,D2y,D3x]; omega
    have hy : (D2y-2)/2=D3y := by dsimp [D2y,D3y]; omega
    simpa only [hx,hy] using hp
  have hD3y6 : 6≤D3y := by dsimp [D3y]; omega
  have hD3yEven : D3y%2=0 := by dsimp [D3y]; omega
  have hD3sum : (D3x+D3y)%8=1 := by dsimp [D3x,D3y]; omega
  have hD4 : BB6.Agent3.CReach D4x D4y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D3x D3y hD3y6 hD3yEven (by omega) (by omega)).mp hD3
    have hx : D3x+D3y-2=D4x := by dsimp [D3x,D3y,D4x]; omega
    have hy : (D3y-2)/2=D4y := by dsimp [D3y,D4y]; omega
    simpa only [hx,hy] using hp
  have hD4y6 : 6≤D4y := by dsimp [D4y]; omega
  have hD4yEven : D4y%2=0 := by dsimp [D4y]; omega
  have hD4sum : (D4x+D4y)%8=1 := by dsimp [D4x,D4y]; omega
  have hD5 : BB6.Agent3.CReach D5x D5y := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D4x D4y hD4y6 hD4yEven (by omega) (by omega)).mp hD4
    have hx : D4x+D4y-2=D5x := by dsimp [D4x,D4y,D5x]; omega
    have hy : (D4y-2)/2=D5y := by dsimp [D4y,D5y]; omega
    simpa only [hx,hy] using hp
  have hD5y6 : 6≤D5y := by dsimp [D5y]; omega
  have hD5yEven : D5y%2=0 := by dsimp [D5y]; omega
  have hD5sum : (D5x+D5y)%8=3 := by dsimp [D5x,D5y]; omega
  have hF : BB6.Agent3.CReach Fx Fy := by
    have hp := (BB6.Agent46.six_even_right_blank_reach_iff
      D5x D5y hD5y6 hD5yEven (by omega) (by omega)).mp hD5
    have hx : D5x+D5y-2=Fx := by dsimp [D5x,D5y,Fx]; omega
    have hy : (D5y-2)/2=Fy := by dsimp [D5y,Fy]; omega
    simpa only [hx,hy] using hp
  have hFy5 : 5≤Fy := by dsimp [Fy]; omega
  have hFyOdd : Fy%2=1 := by dsimp [Fy]; omega
  have hFsum : (Fx+Fy)%4=2 := by dsimp [Fx,Fy]; omega
  exact BB6.Agent11High.blank_no_odd_sum_two
    Fx Fy hFy5 hFyOdd hFsum hF

/-- The original q=0 target is excluded on u=20019+20480*v. -/
theorem w7_q0_target_unreachable_u20019mod20480 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(20019+20480*v)) (17719+28560*(20019+20480*v)) := by
  let u : Nat := 20019+20480*v
  have hq1 : ¬ BB6.Agent3.CReach
      (2*(2228+3591*u)-3) (24450+39417*u) := by
    intro h
    have hx : 2*(2228+3591*u)-3=143780911+147087360*v := by
      dsimp [u]
      omega
    have hy : 24450+39417*u=789113373+807260160*v := by
      dsimp [u]
      omega
    exact w7_z2_q1_parent_unreachable_u20019mod20480 v
      (by simpa only [hx,hy] using h)
  exact w7_q0_target_unreachable_of_q1 u (by dsimp [u]; omega) hq1

#print axioms w7_q0_target_unreachable_of_q1
#print axioms w7_z2_q1_parent_unreachable_u16339mod20480
#print axioms w7_q0_target_unreachable_u16339mod20480
#print axioms w7_z2_q1_parent_unreachable_u20019mod20480
#print axioms w7_q0_target_unreachable_u20019mod20480


/-- The original-source sum-seven parent theorem: every exact parent
    of this target is in the forbidden odd-right sum-two image. -/
theorem w7_blank_no_sum7_target (x y : Nat)
    (hx : 5<x) (hy12 : 12≤y) (hxy8 : (x+y)%8=7)
    (hS16 : (x+y+1)%16=8) (hS32 : (x+y+1)%32=24)
    (hx4 : x%4=3) (hy8 : y%8=4) :
    ¬ BB6.Agent3.CReach x y := by
  intro hreach
  obtain ⟨a,b,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      x y hx hreach
  have hpre : BB6.Agent46.sectionPreimageAll a b x y :=
    (BB6.Agent46.section_preimage_all_iff a b x y).mp hstep
  have himage := BB6.Agent19HighEvenRight.sum7_every_parent_odd_image
    x y a b hy12 hxy8 hS16 hS32 hx4 hy8 hpre
  exact BB6.Agent11High.blank_no_odd_sum_two
    a b himage.1 himage.2.1 himage.2.2 hprev

/-- A tenth new q=1 exclusion, on u=1939+2560*v. The first two
    forced parents reach the original-source sum-seven cylinder. -/
theorem w7_z2_q1_parent_unreachable_u1939mod2560 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (13930351+18385920*v) (76454013+100907520*v) := by
  let Ax : Nat := 13930351+18385920*v
  let Ay : Nat := 76454013+100907520*v
  let Bx : Nat := 45192180+59646720*v
  let By : Nat := 60823095+80277120*v
  let Cx : Nat := 53007635+69961920*v
  let Cy : Nat := 56915364+75119520*v
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
  have hCsum8 : (Cx+Cy)%8=7 := by dsimp [Cx,Cy]; omega
  have hCsum16 : (Cx+Cy+1)%16=8 := by dsimp [Cx,Cy]; omega
  have hCsum32 : (Cx+Cy+1)%32=24 := by dsimp [Cx,Cy]; omega
  have hCx4 : Cx%4=3 := by dsimp [Cx]; omega
  have hCy8 : Cy%8=4 := by dsimp [Cy]; omega
  exact w7_blank_no_sum7_target Cx Cy
    (by dsimp [Cx]; omega) (by dsimp [Cy]; omega)
    hCsum8 hCsum16 hCsum32 hCx4 hCy8 hC

/-- The original q=0 target is excluded on u=1939+2560*v. -/
theorem w7_q0_target_unreachable_u1939mod2560 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(1939+2560*v)) (17719+28560*(1939+2560*v)) := by
  let u : Nat := 1939+2560*v
  have hq1 : ¬ BB6.Agent3.CReach
      (2*(2228+3591*u)-3) (24450+39417*u) := by
    intro h
    have hx : 2*(2228+3591*u)-3=13930351+18385920*v := by
      dsimp [u]
      omega
    have hy : 24450+39417*u=76454013+100907520*v := by
      dsimp [u]
      omega
    exact w7_z2_q1_parent_unreachable_u1939mod2560 v
      (by simpa only [hx,hy] using h)
  exact w7_q0_target_unreachable_of_q1 u (by dsimp [u]; omega) hq1

#print axioms w7_blank_no_sum7_target
#print axioms w7_z2_q1_parent_unreachable_u1939mod2560
#print axioms w7_q0_target_unreachable_u1939mod2560

#print axioms w7_z2_q1_parent_unreachable_u339mod2560
#print axioms w7_q0_target_unreachable_u339mod2560

end BB6.Agent15U5W7U19Mod2560

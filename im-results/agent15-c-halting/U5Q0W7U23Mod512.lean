import U5Q0W7ParentFan
import OddOddLowVal
import EvenEvenUnique
import OddSevenSliver
import Lean.Elab.Tactic.Omega

/-!
A four-edge q=1 parent exclusion in the U5 w=7, z=2 (mod 4) family.
For u=23+512s, the forced ancestry is odd/odd low-value, even/even
unique, odd-seven, odd/odd low-value, then an odd-right sum-one
blank-image obstruction.
-/

namespace BB6.Agent15U5W7U23Mod512
open BB6.Agent46

/-- The q=1 parent is blank-unreachable for u=23+512s. -/
theorem w7_z2_q1_parent_unreachable_u23mod512 (s : Nat) :
    ¬ BB6.Agent3.CReach
      (169639+3677184*s) (931041+20181504*s) := by
  let Ax : Nat := 169639+3677184*s
  let Ay : Nat := 931041+20181504*s
  let Bx : Nat := 550338+11929344*s
  let By : Nat := 740688+16055424*s
  let Cx : Nat := 1291024+27984768*s
  let Cy : Nat := 370343+8027712*s
  let Dx : Nat := 830681+18006240*s
  let Dy : Nat := 600511+13016976*s
  let Ex : Nat := 715594+15511608*s
  let Ey : Nat := 658051+14264292*s
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
  have hByEven : By%2=0 := by dsimp [By]; omega
  have hBy6 : 6≤By := by dsimp [By]; omega
  have hBsum8 : (Bx+By)%8≠0 := by dsimp [Bx,By]; omega
  obtain ⟨a2,k2,hprev2,hstep2⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 Bx By
      (by dsimp [Bx]; omega) hB
  have hBparent :=
    (BB6.Agent46.section_even_even_iff_affine a2 k2 Bx By
      hBxEven hByEven hBy6 hBsum8).mp hstep2
  rcases hBparent with ⟨hsumB,hcostB⟩
  have haC : a2=Cx := by dsimp [Bx,By,Cx] at hsumB ⊢; omega
  have hkC : k2=Cy := by dsimp [By,Cy] at hcostB ⊢; omega
  have hC : BB6.Agent3.CReach Cx Cy := by
    rw [haC,hkC] at hprev2
    exact hprev2
  have hCxEven : Cx%2=0 := by dsimp [Cx]; omega
  have hCyOdd : Cy%2=1 := by dsimp [Cy]; omega
  have hCy5 : 5≤Cy := by dsimp [Cy]; omega
  have hCmod : (Cx+Cy+1)%16=8 := by dsimp [Cx,Cy]; omega
  have hCsize : 23≤Cx+Cy := by dsimp [Cx,Cy]; omega
  obtain ⟨a3,k3,hprev3,hstep3⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 Cx Cy
      (by dsimp [Cx]; omega) hC
  have hCparent :=
    (BB6.Agent3.odd_seven_parent_iff a3 k3 Cx Cy
      hCxEven hCyOdd hCy5 hCmod hCsize).mp hstep3
  rcases hCparent with ⟨hsumC,hcostC⟩
  have haD : a3=Dx := by dsimp [Cx,Cy,Dx] at hsumC ⊢; omega
  have hkD : k3=Dy := by dsimp [Cx,Cy,Dy] at hcostC ⊢; omega
  have hD : BB6.Agent3.CReach Dx Dy := by
    rw [haD,hkD] at hprev3
    exact hprev3
  have hDxOdd : Dx%2=1 := by dsimp [Dx]; omega
  have hDyOdd : Dy%2=1 := by dsimp [Dy]; omega
  have hDy5 : 5≤Dy := by dsimp [Dy]; omega
  have hDsum4 : (Dx+Dy)%4=0 := by dsimp [Dx,Dy]; omega
  have hDsum16 : (Dx+Dy)%16≠0 := by dsimp [Dx,Dy]; omega
  have hDsize : 24≤Dx+Dy := by dsimp [Dx,Dy]; omega
  obtain ⟨a4,k4,hprev4,hstep4⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 Dx Dy hDxOdd hD
  have hDparent :=
    (BB6.Agent3.oddodd_lowval_parent_iff a4 k4 Dx Dy
      hDxOdd hDyOdd hDy5 hDsum4 hDsum16 hDsize).mp hstep4
  rcases hDparent with ⟨hsumD,hcostD⟩
  have haE : a4=Ex := by dsimp [Dx,Dy,Ex] at hsumD ⊢; omega
  have hkE : k4=Ey := by dsimp [Dx,Dy,Ey] at hcostD ⊢; omega
  have hE : BB6.Agent3.CReach Ex Ey := by
    rw [haE,hkE] at hprev4
    exact hprev4
  have hEx5 : 5<Ex := by dsimp [Ex]; omega
  have hEy5 : 5≤Ey := by dsimp [Ey]; omega
  have hEyOdd : Ey%2=1 := by dsimp [Ey]; omega
  have hEsum1 : (Ex+Ey)%4=1 := by dsimp [Ex,Ey]; omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    Ex Ey hEx5 hEy5 hEyOdd hEsum1 hE

/-- The original q=0 target is blank-unreachable on u=23+512s. -/
theorem w7_q0_target_unreachable_u23mod512 (s : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(23+512*s)) (17719+28560*(23+512*s)) := by
  let u : Nat := 23+512*s
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
      dsimp [W,X2,u] at hcost
      omega
    have hbad := BB6.Agent15U5W7Source.w7_z2_q0_parent_unreachable u
    exact hbad (by simpa [W,ha,hk] using hprev)
  · subst n
    have htmp : 8*(a+3)=16*W := by simpa using hscale
    have ha : a=2*W-3 := by omega
    have hk : k=24450+39417*u := by
      rw [ha] at hcost
      dsimp [W,X2,u] at hcost
      omega
    have hax : 2*W-3=169639+3677184*s := by dsimp [W,u]; omega
    have hay : 24450+39417*u=931041+20181504*s := by dsimp [u]; omega
    have hbad := w7_z2_q1_parent_unreachable_u23mod512 s
    rw [ha,hk] at hprev
    exact hbad (by simpa only [hax,hay] using hprev)

#print axioms w7_z2_q1_parent_unreachable_u23mod512
#print axioms w7_q0_target_unreachable_u23mod512
end BB6.Agent15U5W7U23Mod512

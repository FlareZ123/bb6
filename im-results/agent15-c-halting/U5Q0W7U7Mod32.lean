import U5Q0W7ParentFan
import OddOddLowVal
import EvenEvenUnique
import Lean.Elab.Tactic.Omega

/-!
A second q=1 parent exclusion in the U5 w=7, z=2 (mod 4) family.
For u=7+32t the q=1 parent has an odd/odd low-valuation parent,
then an even/even unique parent, then an odd-right sum-one obstruction.
-/

namespace BB6.Agent15U5W7U7Mod32
open BB6.Agent46

/-- The q=1 parent is blank-unreachable for u=7+32t. -/
theorem w7_z2_q1_parent_unreachable_u7mod32 (t : Nat) :
    ¬ BB6.Agent3.CReach
      (54727+229824*t) (300369+1261344*t) := by
  let Ax : Nat := 54727+229824*t
  let Ay : Nat := 300369+1261344*t
  let Bx : Nat := 177546+745584*t
  let By : Nat := 238956+1003464*t
  let Cx : Nat := 416500+1749048*t
  let Cy : Nat := 119477+501732*t
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
  have hCx5 : 5<Cx := by dsimp [Cx]; omega
  have hCy5 : 5≤Cy := by dsimp [Cy]; omega
  have hCyOdd : Cy%2=1 := by dsimp [Cy]; omega
  have hCsum : (Cx+Cy)%4=1 := by dsimp [Cx,Cy]; omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    Cx Cy hCx5 hCy5 hCyOdd hCsum hC

/-- The original q=0 U5 w=7 target is blank-unreachable on u=7+32t. -/
theorem w7_q0_target_unreachable_u7mod32 (t : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(7+32*t)) (17719+28560*(7+32*t)) := by
  let u : Nat := 7+32*t
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
    have hax : 2*W-3=54727+229824*t := by dsimp [W,u]; omega
    have hay : 24450+39417*u=300369+1261344*t := by dsimp [u]; omega
    have hbad := w7_z2_q1_parent_unreachable_u7mod32 t
    rw [ha,hk] at hprev
    exact hbad (by simpa only [hax,hay] using hprev)

#print axioms w7_z2_q1_parent_unreachable_u7mod32
#print axioms w7_q0_target_unreachable_u7mod32
end BB6.Agent15U5W7U7Mod32

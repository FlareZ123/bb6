import U5Q0W7ParentFan
import OddOddLowVal
import OddSevenSliver
import Lean.Elab.Tactic.Omega

/-!
The q=1 parent of the z=2 (mod 4) U5 w=7 cylinder has a further
infinite excluded sublift at u=35 (mod 64).  Its exact source ancestry
is: odd/odd low-valuation parent, then the unique odd-seven parent,
then the original blank odd-right sum-two obstruction.  This file
does not close the whole u=3 (mod 4) class or the full w=7 progression.
-/

namespace BB6.Agent15U5W7U3Mod64
open BB6.Agent46

/-- The q=1 parent is blank-unreachable on u=35+64t. -/
theorem w7_z2_q1_parent_unreachable_u35mod64 (t : Nat) :
    ¬ BB6.Agent3.CReach
      (255823+459648*t) (1404045+2522688*t) := by
  let Ax : Nat := 255823+459648*t
  let Ay : Nat := 1404045+2522688*t
  let Bx : Nat := 829932+1491168*t
  let By : Nat := 1116987+2006928*t
  let Cx : Nat := 973457+1749048*t
  let Cy : Nat := 1045221+1877988*t
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
  have hBx : Bx%2=0 := by dsimp [Bx]; omega
  have hBy : By%2=1 := by dsimp [By]; omega
  have hBy5 : 5≤By := by dsimp [By]; omega
  have hBmod : (Bx+By+1)%16=8 := by dsimp [Bx,By]; omega
  have hBsize : 23≤Bx+By := by dsimp [Bx,By]; omega
  obtain ⟨a2,k2,hprev2,hstep2⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 Bx By
      (by dsimp [Bx]; omega) hB
  have hBparent :=
    (BB6.Agent3.odd_seven_parent_iff a2 k2 Bx By
      hBx hBy hBy5 hBmod hBsize).mp hstep2
  rcases hBparent with ⟨hsumB,hcostB⟩
  have haC : a2=Cx := by dsimp [Bx,By,Cx] at hsumB ⊢; omega
  have hkC : k2=Cy := by dsimp [Bx,By,Cy] at hcostB ⊢; omega
  have hC : BB6.Agent3.CReach Cx Cy := by
    rw [haC,hkC] at hprev2
    exact hprev2
  have hCx : 5<Cx := by dsimp [Cx]; omega
  have hCy5 : 5≤Cy := by dsimp [Cy]; omega
  have hCyOdd : Cy%2=1 := by dsimp [Cy]; omega
  have hCsum : (Cx+Cy)%4=2 := by dsimp [Cx,Cy]; omega
  exact BB6.Agent11High.blank_no_odd_sum_two
    Cx Cy hCy5 hCyOdd hCsum hC

/-- The original q=0 U5 w=7 target is blank-unreachable on u=35+64t.
    The complete source-parent fan leaves only depths zero and two;
    both resulting parents are excluded. -/
theorem w7_q0_target_unreachable_u35mod64 (t : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(35+64*t)) (17719+28560*(35+64*t)) := by
  let u : Nat := 35+64*t
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
         refine ⟨q*(a+3),?_⟩
         rw [hq]
         ac_rfl
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
    have hax : 2*W-3=255823+459648*t := by dsimp [W,u]; omega
    have hay : 24450+39417*u=1404045+2522688*t := by dsimp [u]; omega
    have hbad := w7_z2_q1_parent_unreachable_u35mod64 t
    rw [ha,hk] at hprev
    exact hbad (by simpa only [hax,hay] using hprev)

#print axioms w7_z2_q1_parent_unreachable_u35mod64
#print axioms w7_q0_target_unreachable_u35mod64
end BB6.Agent15U5W7U3Mod64

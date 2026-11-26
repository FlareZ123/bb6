/-
Status: source-level Lean draft; not yet compiled locally.
Scope: the z=2 (mod 4) complete parent fan, its u=1 (mod 4)
exclusion, and the odd-z z=5/13 (mod 16) exclusion. This is not a
closure of the full w=7 progression.
-/

import SectionAllInverse
import M0EvenEvenSumZero
import HighSumTwo
import EvenOddFourExact
import OddEvenUnique
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15U5W7Source
open BB6.Agent46

/-- Complete exact source-parent fan for the even/odd q=0 target
    (P_z) when (z=2+4u). The original source grammar forces an
    odd left parent and an even high-bounce depth. -/
theorem w7_z2_parent_fan (u a k : Nat)
    (hpre : BB6.Agent46.sectionPreimageAll a k
      (17928+28896*u) (17719+28560*u)) :
    ∃ n : Nat, n%2=0 ∧
      2^(n+1)*(a+3)=16*(2228+3591*u) ∧
      2*k+a+7+3*n=53366+86016*u := by
  let x : Nat := 17928+28896*u
  let y : Nat := 17719+28560*u
  let W : Nat := 2228+3591*u
  let X2 : Nat := 53366+86016*u
  have hx : 5<x := by dsimp [x]; omega
  have hy : 5≤y := by dsimp [y]; omega
  have hsumOdd : (x+y)%2=1 := by dsimp [x,y]; omega
  have hT : x+y+1=16*W := by dsimp [x,y,W]; omega
  have hX2 : x+2*y=X2 := by dsimp [x,y,X2]; omega
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [BB6.Agent46.sectionPreimageAll,ha0,hk0] at hpre
    · by_cases hk1 : k=1
      · simp [BB6.Agent46.sectionPreimageAll,ha0,hk0,hk1] at hpre
        omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [BB6.Agent46.sectionPreimageAll,ha0,hk0,hk1] using hpre
        rcases hcase with ⟨_,n,hsum,_⟩
        have hdiv : 8∣x+y := by
          refine ⟨2^n,?_⟩
          simpa [Nat.mul_comm] using hsum
        have hmod : (x+y)%8=0 := Nat.mod_eq_zero_of_dvd hdiv
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hk0] at hpre <;> omega
      · by_cases hk1 : k=1
        · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hk0,hk1] at hpre <;> omega
        · by_cases hk2 : k=2
          · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hpre <;> omega
          · by_cases hk3 : k=3
            · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hpre <;> omega
            · have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                  (2*k-3)+16+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat, x+y+1=2^n*16 ∧
                  (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [BB6.Agent46.sectionPreimageAll,ha0,ha1,
                  hk0,hk1,hk2,hk3] using hpre
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hsum,hcost⟩
              · omega
              · have hcostEven : (x+2*y+2)%2=0 := by
                  rw [hX2]
                  dsimp [X2]
                  omega
                have hnodd : n%2=1 := by omega
                have hnEven : (n+1)%2=0 := by omega
                have hscale : 2^(n+2)*4=16*W := by
                  have hp : 2^(n+2)=2^n*4 := by
                    rw [Nat.pow_add]
                    norm_num
                  calc
                    2^(n+2)*4 = (2^n*4)*4 := by rw [hp]
                    _ = 2^n*16 := by ring
                    _ = 16*W := by
                      have ht : x+y+1=16*W := hT
                      rw [hsum] at ht
                      omega
                have hcost' : 2*k+1+7+3*(n+1)=X2 := by
                  rw [hX2]
                  omega
                exact ⟨n+1,hnEven,hscale,hcost'⟩
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hk0] at hpre <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [BB6.Agent46.sectionPreimageAll,ha0,ha1,hk0,hlow] using hpre
          rcases hcase with ⟨_,hyEq⟩
          omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [BB6.Agent46.sectionPreimageAll,ha0,ha1,
                hk0,hlow,haeven] using hpre
            rcases hcase with ⟨_,n,hsum,_⟩
            have hdiv : 2∣x+y := by
              refine ⟨2^n*(a+2),?_⟩
              rw [hsum]
              have hfactor : 2*(a-1)+6=2*(a+2) := by omega
              rw [hfactor]
              ring
            have hmod : (x+y)%2=0 := Nat.mod_eq_zero_of_dvd hdiv
            omega
          · have haodd : a%2=1 := by omega
            have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat, x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
                simpa [BB6.Agent46.sectionPreimageAll,ha0,ha1,
                  hk0,hlow,haeven] using hpre
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hsum,hcost⟩
            · omega
            · have hfactor : 2*(a-1)+8=2*(a+3) := by omega
              rw [hfactor] at hsum
              have hscale : 2^(n+1)*(a+3)=16*W := by
                have hp : 2^n*(2*(a+3))=2^(n+1)*(a+3) := by
                  rw [Nat.pow_succ]
                  ring
                calc
                  2^(n+1)*(a+3) = 2^n*(2*(a+3)) := by rw [hp]
                  _ = x+y+1 := by symm; exact hsum
                  _ = 16*W := hT
              have hcost' : 2*k+a+7+3*n=X2 := by
                rw [hX2]
                omega
              have hX2even : X2%2=0 := by dsimp [X2]; omega
              have hnEven : n%2=0 := by omega
              exact ⟨n,hnEven,hscale,hcost'⟩

/-- The depth-zero parent of the w=7 z=2 (mod 4) target is
    source-unreachable for every u. -/
theorem w7_z2_q0_parent_unreachable (u : Nat) :
    ¬ BB6.Agent3.CReach
      (8*(2228+3591*u)-3) (17769+28644*u) := by
  apply BB6.Agent11High.blank_no_odd_sum_two
  · omega
  · omega
  · omega

/-- The depth-two parent is source-unreachable when u=1 (mod 4). -/
theorem w7_z2_q1_parent_unreachable (u : Nat) (hu : u%4=1) :
    ¬ BB6.Agent3.CReach
      (2*(2228+3591*u)-3) (24450+39417*u) := by
  apply BB6.Agent11High.blank_no_odd_sum_two
  · omega
  · omega
  · omega

/-- An infinite source-only exclusion for the w=7 q=0 target on
    z=2+4u, u=1 (mod 4). The complete parent fan has only depths
    0 and 2 because W is odd; both parents are excluded by the
    source-certified odd-right sum-two invariant. -/
theorem w7_q0_target_unreachable_u1mod4 (u : Nat) (hu : u%4=1) :
    ¬ BB6.Agent3.CReach
      (17928+28896*u) (17719+28560*u) := by
  let x : Nat := 17928+28896*u
  let y : Nat := 17719+28560*u
  let W : Nat := 2228+3591*u
  let X2 : Nat := 53366+86016*u
  intro hP
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      x y (by dsimp [x]; omega) hP
  have hpre : BB6.Agent46.sectionPreimageAll a k x y :=
    (BB6.Agent46.section_preimage_all_iff a k x y).mp hstep
  obtain ⟨n,hn,hscale,hcost⟩ := w7_z2_parent_fan u a k hpre
  have hWodd : W%2=1 := by dsimp [W]; omega
  have hnle : n≤2 := by
    by_contra hnot
    have hn4 : 4≤n := by omega
    have hpow : 2^5∣2^(n+1) := by
      exact Nat.pow_dvd_pow (a:=2) (m:=5) (n:=n+1) (by omega)
    have hdiv : 32∣2^(n+1)*(a+3) := dvd_mul_of_dvd_left hpow (a+3)
    have hmod : (2^(n+1)*(a+3))%32=0 :=
      Nat.mod_eq_zero_of_dvd hdiv
    rw [hscale] at hmod
    have hmodW : (16*W)%32=16 := by dsimp [W]; omega
    omega
  have hnCases : n=0 ∨ n=2 := by omega
  rcases hnCases with hn0 | hn2
  · subst n
    have ha : a=8*W-3 := by norm_num at hscale; omega
    have hk : k=17769+28644*u := by
      rw [ha] at hcost
      dsimp [W,X2] at hcost
      omega
    have hbad := w7_z2_q0_parent_unreachable u
    exact hbad (by simpa [W,ha,hk] using hprev)
  · subst n
    have ha : a=2*W-3 := by norm_num at hscale; omega
    have hk : k=24450+39417*u := by
      rw [ha] at hcost
      dsimp [W,X2] at hcost
      omega
    have hbad := w7_z2_q1_parent_unreachable u hu
    exact hbad (by simpa [W,ha,hk] using hprev)


/-- The odd-z lifts z=5,13 (mod 16) are also source-unreachable.
    The even/odd four-parent theorem forces Q_z from P_z; the
    odd/even sum-three theorem then forces an odd/odd parent with
    right-odd sum 2 (mod 4), which is excluded by HighSumTwo. -/
theorem w7_q0_target_unreachable_z5or13mod16 (z : Nat)
    (hz : z%16=5 ∨ z%16=13) :
    ¬ BB6.Agent3.CReach (3480+7224*z) (3439+7140*z) := by
  let Px : Nat := 3480+7224*z
  let Py : Nat := 3439+7140*z
  let Qx : Nat := 3457+7182*z
  let Qy : Nat := 3447+7161*z
  let Rx : Nat := 6902+14343*z
  let Ry : Nat := (3445+7161*z)/2
  have hz8 : z%8=5 := by omega
  have hz4 : z%4=1 := by omega
  have hxP : Px%2=0 := by dsimp [Px]; omega
  have hyP : Py%2=1 := by dsimp [Py]; omega
  have hyP5 : 5≤Py := by dsimp [Py]; omega
  have hPmod : (Px+Py+1)%8=4 := by dsimp [Px,Py]; omega
  have hQx : Qx%2=1 := by dsimp [Qx]; omega
  have hQy : Qy%2=0 := by dsimp [Qy]; omega
  have hQy6 : 6≤Qy := by dsimp [Qy]; omega
  have hQsum : (Qx+Qy)%8=3 := by dsimp [Qx,Qy]; omega
  have hQlarge : 5<Qx := by dsimp [Qx]; omega
  have hRy5 : 5≤Ry := by dsimp [Ry]; omega
  have hRyOdd : Ry%2=1 := by dsimp [Ry]; omega
  have hRsum : Rx+Ry=(17249+35847*z)/2 := by
    dsimp [Rx,Ry]
    omega
  have hRsumMod : (Rx+Ry)%4=2 := by
    rw [hRsum]
    omega
  intro hP
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      Px Py (by dsimp [Px]; omega) hP
  have hparent :=
    (BB6.Agent3.evenodd_four_parent_iff a k Px Py
      hxP hyP hyP5 hPmod).mp hstep
  rcases hparent with ⟨hsum,hcost⟩
  have ha : a=Qx := by
    dsimp [Px,Py,Qx] at hsum ⊢
    omega
  have hk : k=Qy := by
    dsimp [Px,Py,Qy] at hcost ⊢
    omega
  have hQ : BB6.Agent3.CReach Qx Qy := by
    rw [ha,hk] at hprev
    exact hprev
  obtain ⟨a2,k2,hprev2,hstep2⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      Qx Qy hQlarge hQ
  have hparent2 :=
    (BB6.Agent46.section_odd_even_iff_affine a2 k2 Qx Qy
      hQx hQy hQy6 hQsum).mp hstep2
  rcases hparent2 with ⟨ha2,hk2⟩
  have haR : a2=Rx := by
    dsimp [Rx,Qx,Qy] at ha2 ⊢
    omega
  have hkR : k2=Ry := by
    dsimp [Ry,Qy] at hk2 ⊢
    omega
  rw [haR,hkR] at hprev2
  exact BB6.Agent11High.blank_no_odd_sum_two Rx Ry hRy5 hRyOdd hRsumMod hprev2


/-- The q=1 parent on the root-index lift u=59 (mod 80) has a
    unique odd/odd low-valuation predecessor with odd right coordinate
    and sum 1 (mod 4), so it is outside the authentic blank orbit. -/
theorem w7_z2_q1_parent_unreachable_u59mod80 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (428191+574560*v) (2350053+3153360*v) := by
  let Ax : Nat := 428191+574560*v
  let Ay : Nat := 2350053+3153360*v
  let Bx : Nat := 1389120+1863960*v
  let By : Nat := 1869585+2508660*v
  have hAx : 5<Ax := by dsimp [Ax]; omega
  have hAxodd : Ax%2=1 := by dsimp [Ax]; omega
  have hAyodd : Ay%2=1 := by dsimp [Ay]; omega
  have hAy5 : 5≤Ay := by dsimp [Ay]; omega
  have hAsum : (Ax+Ay)%8=4 := by dsimp [Ax,Ay]; omega
  have hBx : 5<Bx := by dsimp [Bx]; omega
  have hBy5 : 5≤By := by dsimp [By]; omega
  have hByodd : By%2=1 := by dsimp [By]; omega
  have hBsum : (Bx+By)%4=1 := by dsimp [Bx,By]; omega
  intro hA
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      Ax Ay hAx hA
  have hparent := (BB6.Agent3.oddodd_parent_iff a k Ax Ay
    hAxodd hAyodd hAy5 hAsum).mp hstep
  rcases hparent with ⟨hsum,hcost⟩
  have ha : a=Bx := by
    dsimp [Ax,Ay,Bx] at hsum ⊢
    omega
  have hk : k=By := by
    dsimp [Ax,Ay,By] at hcost ⊢
    omega
  have hB : BB6.Agent3.CReach Bx By := by
    rw [ha,hk] at hprev
    exact hprev
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    Bx By hBx hBy5 hByodd hBsum hB

/-- The complete z=2 (mod 4) parent fan also closes the higher-depth
    lift u=59+80v. Here W is odd, so only n=0,2 occur; n=0 is
    excluded by the universal sum-two invariant and n=2 by the
    preceding low-valuation parent chain. This is the w=439 (mod 512)
    root-index subcylinder after the exact residual congruence. -/
theorem w7_q0_target_unreachable_u59mod80 (v : Nat) :
    ¬ BB6.Agent3.CReach
      (17928+28896*(59+80*v)) (17719+28560*(59+80*v)) := by
  let u : Nat := 59+80*v
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
    w7_z2_parent_fan u a k hpre
  have hWodd : W%2=1 := by dsimp [W,u]; omega
  have hnle : n≤2 := by
    by_contra hnot
    have hn4 : 4≤n := by omega
    have hpow : 32∣2^(n+1) := by
      change 2^5∣2^(n+1)
      exact Nat.pow_dvd_pow 2 (by omega)
    have hdiv : 32∣2^(n+1)*(a+3) :=
      dvd_mul_of_dvd_left hpow (a+3)
    have hmod : (2^(n+1)*(a+3))%32=0 :=
      Nat.mod_eq_zero_of_dvd hdiv
    rw [hscale] at hmod
    have hmodW : (16*W)%32=16 := by
      obtain ⟨q,hq⟩ : ∃ q, W=2*q+1 := by omega
      rw [hq]
      omega
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
    have hbad := w7_z2_q0_parent_unreachable u
    exact hbad (by simpa [W,ha,hk] using hprev)
  · subst n
    have ha : a=2*W-3 := by
      have htmp : 8*(a+3)=16*W := by simpa using hscale
      omega
    have hk : k=24450+39417*u := by
      rw [ha] at hcost
      dsimp [W,X2] at hcost
      omega
    have hbad := w7_z2_q1_parent_unreachable_u59mod80 v
    have hprev' : BB6.Agent3.CReach
        (428191+574560*v) (2350053+3153360*v) := by
      simpa [u,W,ha,hk] using hprev
    exact hbad hprev'


#print axioms w7_q0_target_unreachable_z5or13mod16

#print axioms w7_z2_parent_fan
#print axioms w7_z2_q0_parent_unreachable
#print axioms w7_z2_q1_parent_unreachable
#print axioms w7_q0_target_unreachable_u1mod4

end BB6.Agent15U5W7Source

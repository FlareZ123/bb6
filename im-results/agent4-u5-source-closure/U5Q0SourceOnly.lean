import U5Q0OddOddFan
import U5Q0M16Residual
import EvenEvenParentFan
import EvenOddFourExact
import OddOddVal3Orbit
import M0EvenEvenSumZero
import HighSumTwo
import Lean.Elab.Tactic.Omega

/-!
Source-only closure of the two U5 q=0 inverse cylinders used by the
w=21 (mod 32) and w=37 (mod 128) residuals.

Unlike the M16 quotient route, the proof below uses only the exact
original-section predecessor grammar and already certified blank-image
invariants. The new file is a Lean draft pending exact-source preflight.
-/

namespace BB6.Agent4U5SourceOnly
open BB6.Agent3
open BB6.Agent46

/-- If an even/even blank-reachable target has coordinate sum 2 mod 4,
its only possible original-section parent is the direct parent. The
zero-left and even-a bounce alternatives have sum divisible by four. -/
private theorem even_even_sum_two_reach_implies_direct
    (x y : Nat) (hx : 5 < x) (hxe : x%2=0)
    (hy : 6≤y) (hye : y%2=0) (hsum : (x+y)%4=2)
    (hr : CReach x y) :
    CReach (x+y-2) ((y-2)/2) := by
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  have hfan := BB6.Agent3ParentFan.even_even_parent_fan
    a k x y (by omega) hxe hy hye hstep
  rcases hfan with hdirect | hzero | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    simpa only [ha,hk] using hprev
  · rcases hzero with ⟨_,_,n,hxy,_⟩
    have hmod : (2^n*8)%4=0 := by simp [Nat.mul_mod]
    rw [hxy] at hsum
    omega
  · rcases hbounce with ⟨_,_,_,_,n,hn,hxy,_⟩
    have hdiv : 4∣2^(n+1) := by
      change 2^2∣2^(n+1)
      exact Nat.pow_dvd_pow 2 (by omega)
    have hpowmod : (2^(n+1))%4=0 :=
      Nat.mod_eq_zero_of_dvd hdiv
    have hmod : (2^(n+1)*(a+2))%4=0 := by
      simp [Nat.mul_mod,hpowmod]
    rw [hxy] at hsum
    omega

/-- Source-only all-time exclusion of X_t=(44t-1,42t-1) for
t=19 mod 32. The exact parent fan has q=0,1 only; both parents reduce
to already forbidden odd-right sum-one states. No finite quotient is
used. -/
theorem q0_X_not_reach_t19 (n : Nat) :
    ¬ CReach (44*(32*n+19)-1) (42*(32*n+19)-1) := by
  intro hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*(32*n+19)-1) (42*(32*n+19)-1) (by omega) hX
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
    (32*n+19) a k (by omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hNmod : (43*(32*n+19)-1)%32=16 := by omega
  have hqle : q≤1 := by
    by_contra hnot
    have hq2 : 2≤q := by omega
    have hdiv16 : 4^2∣4^q := Nat.pow_dvd_pow 4 hq2
    rcases hdiv16 with ⟨r,hr⟩
    obtain ⟨v,hv⟩ : ∃ v, U=2*v := ⟨U/2,by omega⟩
    have hdiv32 : 32∣4^q*U := by
      refine ⟨r*v,?_⟩
      calc
        4^q*U=(4^2*r)*(2*v) := by rw [hr,hv]
        _=(4*4*2)*(r*v) := by
          rw [show (4:Nat)^2=4*4 by decide]
          ac_rfl
        _=32*(r*v) := by
          rw [show (4:Nat)*4*2=32 by decide]
    have hNdiv : 32∣43*(32*n+19)-1 := by
      rw [hpow]
      exact hdiv32
    have hNzero : (43*(32*n+19)-1)%32=0 :=
      Nat.mod_eq_zero_of_dvd hNdiv
    omega
  have hqCases : q=0 ∨ q=1 := by omega
  rcases hqCases with hq0 | hq1
  · have hU : U=43*(32*n+19)-1 := by
      simpa [hq0] using hpow.symm
    have haEq : a=1376*n+814 := by rw [hU] at ha; omega
    have hkEq : k=1360*n+804 := by rw [hU] at hcost; omega
    have hP : CReach (1376*n+814) (1360*n+804) := by
      simpa only [haEq,hkEq] using hprev
    have hdirect := even_even_sum_two_reach_implies_direct
      (1376*n+814) (1360*n+804)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP
    have hx : (1376*n+814)+(1360*n+804)-2 =
        2736*n+1616 := by omega
    have hy : ((1360*n+804)-2)/2=680*n+401 := by omega
    have hforced : CReach (2736*n+1616) (680*n+401) := by
      simpa only [hx,hy] using hdirect
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (2736*n+1616) (680*n+401)
      (by omega) (by omega) (by omega) (by omega) hforced
  · have hU : 4*U=43*(32*n+19)-1 := by
      simpa [hq1] using hpow.symm
    have hUeq : U=344*n+204 := by omega
    have haEq : a=344*n+202 := by rw [hUeq] at ha; omega
    have hkEq : k=1876*n+1107 := by rw [hUeq] at hcost; omega
    have hP : CReach (344*n+202) (1876*n+1107) := by
      simpa only [haEq,hkEq] using hprev
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (344*n+202) (1876*n+1107)
      (by omega) (by omega) (by omega) (by omega) hP

/-- Source-only all-time exclusion of X_t=(44t-1,42t-1) for
t=99 mod 128. The exact parent fan has q=0,1,2 only. The q=0
parent reduces to sum-one; q=1 has a unique even/odd parent in the
forbidden odd/odd sum-two image; q=2 is itself odd-right sum-one. -/
theorem q0_X_not_reach_t99 (n : Nat) :
    ¬ CReach (44*(128*n+99)-1) (42*(128*n+99)-1) := by
  intro hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*(128*n+99)-1) (42*(128*n+99)-1) (by omega) hX
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
    (128*n+99) a k (by omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hNmod : (43*(128*n+99)-1)%64=32 := by omega
  have hqle : q≤2 := by
    by_contra hnot
    have hq3 : 3≤q := by omega
    have hdiv64 : 4^3∣4^q := Nat.pow_dvd_pow 4 hq3
    rcases hdiv64 with ⟨r,hr⟩
    have hNdiv : 64∣43*(128*n+99)-1 := by
      refine ⟨r*U,?_⟩
      calc
        43*(128*n+99)-1=4^q*U := hpow
        _=(4^3*r)*U := by rw [hr]
        _=64*(r*U) := by
          rw [show (4:Nat)^3=64 by decide]
          ac_rfl
    have hNzero : (43*(128*n+99)-1)%64=0 :=
      Nat.mod_eq_zero_of_dvd hNdiv
    omega
  have hqCases : q=0 ∨ q=1 ∨ q=2 := by omega
  rcases hqCases with hq0 | hq1 | hq2
  · have hU : U=43*(128*n+99)-1 := by
      simpa [hq0] using hpow.symm
    have haEq : a=5504*n+4254 := by rw [hU] at ha; omega
    have hkEq : k=5440*n+4204 := by rw [hU] at hcost; omega
    have hP : CReach (5504*n+4254) (5440*n+4204) := by
      simpa only [haEq,hkEq] using hprev
    have hdirect := even_even_sum_two_reach_implies_direct
      (5504*n+4254) (5440*n+4204)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP
    have hx : (5504*n+4254)+(5440*n+4204)-2 =
        10944*n+8456 := by omega
    have hy : ((5440*n+4204)-2)/2=2720*n+2101 := by omega
    have hforced : CReach (10944*n+8456) (2720*n+2101) := by
      simpa only [hx,hy] using hdirect
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (10944*n+8456) (2720*n+2101)
      (by omega) (by omega) (by omega) (by omega) hforced
  · have hU : 4*U=43*(128*n+99)-1 := by
      simpa [hq1] using hpow.symm
    have hUeq : U=1376*n+1064 := by omega
    have haEq : a=1376*n+1062 := by rw [hUeq] at ha; omega
    have hkEq : k=7504*n+5797 := by rw [hUeq] at hcost; omega
    have hP : CReach (1376*n+1062) (7504*n+5797) := by
      simpa only [haEq,hkEq] using hprev
    have hmod : ((1376*n+1062)+(7504*n+5797)+1)%8=4 := by omega
    have hforced := (BB6.Agent3.evenodd_four_blank_reach_iff
      (1376*n+1062) (7504*n+5797)
      (by omega) (by omega) (by omega) hmod).mp hP
    have hx : ((1376*n+1062)+(7504*n+5797)-5)/2 =
        4440*n+3427 := by omega
    have hy : ((1376*n+1062)+3*(7504*n+5797)-9)/4 =
        5972*n+4611 := by omega
    have hancestor : CReach (4440*n+3427) (5972*n+4611) := by
      change (∃ j, BB6.Agent8Section.run BB6.Agent46.secNext j
        (some (5,1))=some (4440*n+3427,5972*n+4611))
      simpa only [hx,hy] using hforced
    exact BB6.Agent11High.blank_no_odd_sum_two
      (4440*n+3427) (5972*n+4611)
      (by omega) (by omega) (by omega) hancestor
  · have hU : 16*U=43*(128*n+99)-1 := by
      simpa [hq2] using hpow.symm
    have hUeq : U=344*n+266 := by omega
    have haEq : a=344*n+264 := by rw [hUeq] at ha; omega
    have hkEq : k=8020*n+6193 := by rw [hUeq] at hcost; omega
    have hP : CReach (344*n+264) (8020*n+6193) := by
      simpa only [haEq,hkEq] using hprev
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (344*n+264) (8020*n+6193)
      (by omega) (by omega) (by omega) (by omega) hP

/-- The two exact inverse edges from the terminal U5 q=0 parent
(64*t+5,32*t+3) to X_t=(44*t-1,42*t-1). -/
private theorem q0_parent_reach_implies_X (t : Nat) (ht : 1≤t)
    (h : CReach (64*t+5) (32*t+3)) :
    CReach (44*t-1) (42*t-1) := by
  have h1 := (BB6.Agent3.oddodd_val3_blank_reach_iff
    (64*t+5) (32*t+3)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h
  have h1' : CReach (48*t+2) (40*t+1) := by
    have hx : ((64*t+5)+(32*t+3)-4)/2=48*t+2 := by omega
    have hy : ((64*t+5)+3*(32*t+3)-10)/4=40*t+1 := by omega
    simpa only [hx,hy] using h1
  have h2 := (BB6.Agent3.evenodd_four_blank_reach_iff
    (48*t+2) (40*t+1)
    (by omega) (by omega) (by omega) (by omega)).mp h1'
  have h2' : CReach (44*t-1) (42*t-1) := by
    have hx : ((48*t+2)+(40*t+1)-5)/2=44*t-1 := by omega
    have hy : ((48*t+2)+3*(40*t+1)-9)/4=42*t-1 := by omega
    change (∃ j, BB6.Agent8Section.run BB6.Agent46.secNext j
      (some (5,1))=some (44*t-1,42*t-1))
    simpa only [hx,hy] using h2
  exact h2'

/-- The U5 q=0 parent is unreachable on w=21 mod 32 without the
M16 quotient: the residual forces t=19 mod 32, and the exact
source-only predecessor fan excludes X_t. -/
theorem blank_no_u5_q0_parent_w21 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%32=21)
    (ht : 1≤t)
    (hparent : CReach (64*t+5) (32*t+3)) : False := by
  have hX := q0_parent_reach_implies_X t ht hparent
  have htmod := BB6.Agent3U5M16Residual.u5_m8_t_mod32
    w s m t hs hm hp hw
  obtain ⟨n,hn⟩ : ∃ n, t=32*n+19 := by
    refine ⟨t/32,?_⟩
    omega
  exact q0_X_not_reach_t19 n (by simpa only [hn] using hX)

/-- The U5 q=0 parent is unreachable on w=37 mod 128 without the
M16 quotient: the residual forces t=99 mod 128, and the exact
source-only predecessor fan excludes X_t. -/
theorem blank_no_u5_q0_parent_w37 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%128=37)
    (ht : 1≤t)
    (hparent : CReach (64*t+5) (32*t+3)) : False := by
  have hX := q0_parent_reach_implies_X t ht hparent
  have htmod := BB6.Agent3U5M16Residual.u5_m8_t_mod128_w37
    w s m t hs hm hp hw
  obtain ⟨n,hn⟩ : ∃ n, t=128*n+99 := by
    refine ⟨t/128,?_⟩
    omega
  exact q0_X_not_reach_t99 n (by simpa only [hn] using hX)

#print axioms even_even_sum_two_reach_implies_direct
#print axioms q0_X_not_reach_t19
#print axioms q0_X_not_reach_t99
#print axioms blank_no_u5_q0_parent_w21
#print axioms blank_no_u5_q0_parent_w37

end BB6.Agent4U5SourceOnly

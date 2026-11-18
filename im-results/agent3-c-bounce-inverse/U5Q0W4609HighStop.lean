import U5ResidualArithmetic
import U5Q0M16Residual
import U5Y3M8
import U5Q0SecondaryH40
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
Source-only high-stop closure draft for the U5 residual cylinder
w = 4609 (mod 8192). The strengthened q=0 secondary parent analysis
reduces t to 2599 (mod 8192), where the only secondary fan depths
are r=1,2,3 and every parent is excluded by exact source inverses.

Intermediate proof draft pending exact local preflight and CI.
-/

namespace BB6.Agent3U5Q04609HighStop

open BB6.Agent3
open BB6.Agent46
open BB6.Agent3U5DepthFan
open BB6.Agent3U5M16Residual
open BB6.Agent11High

private theorem succ_le_two_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : 2^(n+1)=2^n*2 := by rw [Nat.pow_succ]
      omega

/-- The residual equations force t=2599 (mod 8192) on the
w=4609 (mod 8192) cylinder. -/
theorem u5_m8_t_mod8192_w4609 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%8192=4609) : t%8192=2599 := by
  have hid := u5_m8_t_identity w s m t hs hm hp
  have hdiv : 8192∣20*2^(201+3360*w) := by
    refine ⟨20*2^(188+3360*w),?_⟩
    have hexp : 201+3360*w=13+(188+3360*w) := by omega
    calc
      20*2^(201+3360*w)
          =20*(2^13*2^(188+3360*w)) := by rw [hexp,Nat.pow_add]
      _ =8192*(20*2^(188+3360*w)) := by
            norm_num [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hmod8192 :
      (211*t+1360+22155*w)%8192=0 := by
    rw [hid]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hmodR :
      (211*(t%8192)+1360+22155*4609)%8192=0 := by
    simpa [Nat.add_mod,Nat.mul_mod,Nat.mod_mod,hw] using hmod8192
  let r := t%8192
  have hdivR : 8192∣211*r+1360+22155*4609 := by
    apply Nat.dvd_of_mod_eq_zero
    simpa [r] using hmodR
  obtain ⟨q,hq⟩ := hdivR
  have hrbound : r<8192 := by
    dsimp [r]
    exact Nat.mod_lt _ (by decide)
  have hrEq : r=2599 := by omega
  have ht8192 : t%8192=2599 := by simpa [r] using hrEq
  exact ht8192

/-- Pulling the q=0 terminal parent through the two exact
source inverses gives the odd/odd state X_t. -/
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
    simpa only [hx,hy] using h2
  exact h2'

/-- The q=0 parent is excluded when t=2599 (mod 8192):
the unique odd/odd low-value parent is P0 with h=40 (mod 128),
already excluded by the complete secondary parent fan. -/
theorem blank_no_u5_q0_parent_t2599 (t : Nat)
    (ht : t%8192=2599) :
    ¬ CReach (64*t+5) (32*t+3) := by
  let u := t/8192
  have hdecomp : t=8192*(t/8192)+2599 := by
    have h := Nat.mod_add_div t 8192
    omega
  have htEq : t=39+64*(40+128*u) := by
    dsimp [u]
    omega
  have hP0not :=
    BB6.Agent3U5Q0H40.u5_q0_secondary_parent_unreachable_h40 u
  have hXnot : ¬ CReach (44*t-1) (42*t-1) := by
    intro hX
    have hiff := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (44*t-1) (42*t-1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hX
    have hx :
        ((44*t-1)+(42*t-1)-4)/2=43*t-3 := by omega
    have hy :
        ((44*t-1)+3*(42*t-1)-10)/4=(85*t-7)/2 := by omega
    have hparent : CReach (43*t-3) ((85*t-7)/2) := by
      simpa only [hx,hy] using hiff
    have hxP : 43*t-3=111754+352256*u := by
      rw [htEq]
      omega
    have hyP : (85*t-7)/2=110454+348160*u := by
      rw [htEq]
      omega
    have hP0 : CReach
        (111754+352256*u) (110454+348160*u) := by
      simpa only [hxP,hyP] using hparent
    exact hP0not hP0
  intro hparent
  exact hXnot (q0_parent_reach_implies_X t (by omega) hparent)

/-- The q=0 parent of the y=3 U5 terminal is excluded on
w=4609 (mod 8192). -/
theorem blank_no_u5_q0_parent_w4609_8192 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%8192=4609) :
    ¬ CReach (8*(m+1)-3) (4*(m+1)-1) := by
  have htmod := u5_m8_t_mod8192_w4609 w s m t hs hm hp hw
  have hnot := blank_no_u5_q0_parent_t2599 t htmod
  intro hparent
  have hx : 8*(m+1)-3=64*t+5 := by omega
  have hy : 4*(m+1)-1=32*t+3 := by omega
  have hparent' : CReach (64*t+5) (32*t+3) := by
    simpa only [hx,hy] using hparent
  exact hnot hparent'

private theorem q1_parent_unreachable (p : Nat)
    (hp8 : p%8=1) (hpge : 3≤p) :
    ¬ CReach (2*p-3) (7*p-4) := by
  apply BB6.Agent11High.blank_no_odd_sum_two
  · omega
  · omega
  · omega

/-- The remaining y=3 terminal of the U5 M8 residual is
unreachable on w=1 (mod 8192): q=0 uses the exact nested
source fan and dyadic cone; q=1 uses the odd-right sum-two
invariant, and q>=2 contradicts p=1 (mod 8). -/
theorem blank_no_u5_residual_m8w_w4609_8192 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%8192=4609) :
    ¬ CReach (302+512*s-4*(201+3360*w)) 3 := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  have hm' : 32*s=32+105*(8*w)+m := by omega
  have hm8 : m%8=0 := by
    have hmod : (32*s)%8=(32+840*w+m)%8 := by rw [hm]
    have hleft : (32*s)%8=0 := by simp [Nat.mul_mod]
    have hright : (32+840*w+m)%8=m%8 := by
      simp [Nat.add_mod,Nat.mul_mod]
    rw [hleft,hright] at hmod
    exact hmod.symm
  have hp8 : (m+1)%8=1 := by simp [Nat.add_mod,hm8]
  have hrpow : 201+3360*w+1≤2^(201+3360*w) :=
    succ_le_two_pow _
  have hlin : 211*(27*w+1)+129≤5*(201+3360*w+1) := by omega
  have hbig : 211*(27*w+1)+129≤5*2^(201+3360*w) := by
    calc
      211*(27*w+1)+129 ≤ 5*(201+3360*w+1) := hlin
      _ ≤ 5*2^(201+3360*w) := Nat.mul_le_mul_left 5 hrpow
  have hsge : 27*w+1≤s := by omega
  have hmge : 24*w≤m := by omega
  have hwge : 1≤w := by omega
  have hpge : 3≤m+1 := by omega
  intro hreach
  obtain ⟨time,ht⟩ := hreach
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
  | succ n =>
      cases hr : BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hr] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : BB6.Agent46.secNext (a,k)=
              some (302+512*s-4*(201+3360*w),3) := by
            simpa [BB6.Agent8Section.run,hr] using ht
          have hM : 201+420*(8*w)=201+3360*w := by omega
          have hsec : BB6.Agent46.secNext (a,k)=
              some (302+512*s-4*(201+420*(8*w)),3) := by
            simpa only [hM] using hedge
          rcases u5_residual_y3_parent_fan (8*w) s m a k hs' hm' hsec with
            hq0 | ⟨q,U,hqpos,hqbound,hdecomp,ha,hk⟩
          · have hparent0 : CReach (8*(m+1)-3) (4*(m+1)-1) := by
              rw [hq0.1,hq0.2] at hr
              exact ⟨n,hr⟩
            let t := (m+1)/8
            have hp : m+1=8*t+1 := by dsimp [t]; omega
            exact blank_no_u5_q0_parent_w4609_8192 w s m t hs hm hp hw hparent0
          · by_cases hq1 : q=1
            · subst q
              have hUeq : U=m+1 := by simpa using hdecomp.symm
              have haEq : a=2*(m+1)-3 := by omega
              have hkEq : k=7*(m+1)-4 := by omega
              have hparent : CReach (2*(m+1)-3) (7*(m+1)-4) := by
                rw [haEq,hkEq] at hr
                exact ⟨n,hr⟩
              exact q1_parent_unreachable (m+1) hp8 hpge hparent
            · have hq2 : 2≤q := by omega
              have h4pow : 4∣2^(2*q-2) := by
                change 2^2∣2^(2*q-2)
                exact Nat.pow_dvd_pow 2 (by omega)
              rcases h4pow with ⟨r,hrpow⟩
              have h4 : 4∣m+1 := by
                refine ⟨r*U,?_⟩
                rw [hdecomp,hrpow]
                ac_rfl
              have h4mod : (m+1)%4=0 := Nat.mod_eq_zero_of_dvd h4
              omega

/-- The B_s feeder of the authentic high m=0 stop is
unreachable on w=1 (mod 8192). -/
theorem blank_no_u5_B_s_m8w_w4609_8192 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%8192=4609) :
    ¬ CReach (54+90*s) (127+211*s) := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  intro hB
  have hterminal :=
    (BB6.Agent3U5M8.u5_residual_six_even_right_chain (8*w) s hs').mp hB
  have hM : 201+420*(8*w)=201+3360*w := by omega
  have hterminal' : CReach (302+512*s-4*(201+3360*w)) 3 := by
    simpa only [hM] using hterminal
  exact blank_no_u5_residual_m8w_w4609_8192 w s m hs hm hw hterminal'

/-- Both exact source parents of A_s are excluded on
w=1 (mod 8192). -/
theorem blank_no_u5_A_s_m8w_w4609_8192 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%8192=4609) :
    ¬ CReach (130+208*s) (94+152*s) := by
  have hdiv : 8∣2^(201+3360*w) := by
    change 2^3∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod : (2^(201+3360*w))%8=0 := Nat.mod_eq_zero_of_dvd hdiv
  have hsmod : (211*s+129)%8=0 := by
    rw [hs,Nat.mul_mod,hpowmod]
  have hs8 : s%8=5 := by omega
  have hL := BB6.Agent11M0SumZeroVerified.blank_no_L_s_mod8_five s hs8
  have hB := blank_no_u5_B_s_m8w_w4609_8192 w s m hs hm hw
  intro hA
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (130+208*s) (94+152*s) (by omega) hA
  have hfan := BB6.Agent11M0SumZeroVerified.m0_odd_ray_parent
    s a k (by omega) hstep
  rcases hfan with hLparent | hBparent
  · have hLreach : CReach (222+360*s) (46+76*s) := by
      rw [hLparent.1,hLparent.2] at hprev
      exact hprev
    exact hL hLreach
  · have hBreach : CReach (54+90*s) (127+211*s) := by
      rw [hBparent.1,hBparent.2] at hprev
      exact hprev
    exact hB hBreach

/-- The authentic blank-root high m=0 stopping state j=39+64*s
is excluded for the entire nonempty U5 residual cylinder
w=1 (mod 8192). -/
theorem blank_no_high_m0_u5_w4609_8192 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%8192=4609) :
    ¬ CReach (2*(39+64*s)+3) (3*(39+64*s)+7) := by
  intro hroot
  let t := 2*s+1
  have hroot' : CReach (17+64*t) (28+96*t) := by
    have hx : 2*(39+64*s)+3=17+64*t := by dsimp [t]; omega
    have hy : 3*(39+64*s)+7=28+96*t := by dsimp [t]; omega
    simpa only [hx,hy] using hroot
  have hA := BB6.Agent11M0SumZeroVerified.mzero_first_two_reach t hroot'
  have hx : 26+104*t=130+208*s := by dsimp [t]; omega
  have hy : 18+76*t=94+152*s := by dsimp [t]; omega
  have hA' : CReach (130+208*s) (94+152*s) := by
    simpa only [hx,hy] using hA
  exact blank_no_u5_A_s_m8w_w4609_8192 w s m hs hm hw hA'

/-- Nonvacuity: every n supplies an actual residual solution and
an excluded authentic blank-root state in the w=1 mod8192
subcylinder.  The existing residual monotonicity theorem makes
the resulting roots pairwise distinct. -/
theorem every_w4609_8192_residual_has_unreachable_root (n : Nat) :
    ∃ s m,
      211*s+129=5*2^(201+3360*(8192*n+4609)) ∧
      32*s=32+840*(8192*n+4609)+m ∧
      (39+64*s)%32768=18791 ∧
      (1+2*s)%1024=587 ∧
      ¬ CReach (2*(39+64*s)+3) (3*(39+64*s)+7) := by
  obtain ⟨s,m,hs,hm,_,_⟩ :=
    BB6.Agent3U5ResidualArithmetic.u5_residual_nonempty
      (8192*n+4609)
  have hw : (8192*n+4609)%8192=4609 := by omega
  have hroot := blank_no_high_m0_u5_w4609_8192
    (8192*n+4609) s m hs hm hw
  have hres :=
    BB6.Agent3U5ResidualArithmetic.u5_high_root_parameter_residue
      (8192*n+4609) s hs
  exact ⟨s,m,hs,hm,hres.1,hres.2,hroot⟩

/-- The excluded roots on distinct w parameters are strictly
increasing, hence this source-excluded cylinder is infinite. -/
theorem w4609_8192_roots_pairwise_distinct
    (n1 n2 s1 s2 : Nat)
    (hn : n1<n2)
    (hs1 : 211*s1+129=5*2^(201+3360*(8192*n1+4609)))
    (hs2 : 211*s2+129=5*2^(201+3360*(8192*n2+4609))) :
    39+64*s1 < 39+64*s2 := by
  have hw : 8192*n1+4609 < 8192*n2+4609 := by omega
  have hslt :=
    BB6.Agent3U5ResidualArithmetic.u5_residual_s_strict_mono
      (8192*n1+4609) (8192*n2+4609) s1 s2 hw hs1 hs2
  omega

#print axioms u5_m8_t_mod8192_w4609
#print axioms blank_no_u5_q0_parent_t2599
#print axioms blank_no_u5_q0_parent_w4609_8192
#print axioms blank_no_u5_residual_m8w_w4609_8192
#print axioms blank_no_u5_B_s_m8w_w4609_8192
#print axioms blank_no_u5_A_s_m8w_w4609_8192
#print axioms blank_no_high_m0_u5_w4609_8192
#print axioms every_w4609_8192_residual_has_unreachable_root
#print axioms w4609_8192_roots_pairwise_distinct

end BB6.Agent3U5Q04609HighStop

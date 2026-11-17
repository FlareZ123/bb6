import U5Q0M32W485HighStop
import U5Q0OddOddFan
import U5Q0M16Residual
import DyadicSixCone
import GeneralMod8SectionRest
import SevenInverse

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent3U5Q0W1821HighStop

open BB6.Agent3
open BB6.Agent46
open BB6.Agent3U5DepthFan
open BB6.Agent3U5Q0Fan
open BB6.Agent3U5M16Residual
open BB6.Agent11High

private theorem succ_le_two_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpow : 2^(n+1)=2^n*2 := by rw [Nat.pow_succ]
    omega

/-- The U5 M8 residual fixes t modulo 2048 on the
w=1821 (mod 2048) cylinder.  This is the only residue
needed for the q=0/q=1 parent exclusion below. -/
theorem u5_m8_t_mod2048_w1821 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%2048=1821) : t%2048=427 := by
  have hid := u5_m8_t_identity w s m t hs hm hp
  have hdiv : 2048∣20*2^(201+3360*w) := by
    refine ⟨20*2^(190+3360*w),?_⟩
    have hexp : 201+3360*w=11+(190+3360*w) := by omega
    calc
      20*2^(201+3360*w)
          =20*(2^11*2^(190+3360*w)) := by rw [hexp,Nat.pow_add]
      _ =2048*(20*2^(190+3360*w)) := by
            norm_num [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hmod2048 :
      (211*t+1360+22155*w)%2048=0 := by
    rw [hid]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hmodR :
      (211*(t%2048)+1360+22155*1821)%2048=0 := by
    simpa [Nat.add_mod,Nat.mul_mod,Nat.mod_mod,hw] using hmod2048
  let r := t%2048
  have hdivR : 2048∣211*r+1360+22155*1821 := by
    apply Nat.dvd_of_mod_eq_zero
    simpa [r] using hmodR
  obtain ⟨q,hq⟩ := hdivR
  have hinv : 211*1883=1+2048*194 := by norm_num
  have hconst :
      1883*(1360+22155*1821)+427=2048*37095114 := by norm_num
  have hEq :
      r+2048*(194*r+37095114)=427+2048*(1883*q) := by
    calc
      r+2048*(194*r+37095114)
          =(1+2048*194)*r+2048*37095114 := by ring
      _ =(211*1883)*r+
          1883*(1360+22155*1821)+427 := by
            rw [hinv,hconst]
            ring
      _ =1883*(211*r+1360+22155*1821)+427 := by ring
      _ =1883*(2048*q)+427 := by rw [hq]
      _ =427+2048*(1883*q) := by ring
  have hrbound : r<2048 := by
    dsimp [r]
    exact Nat.mod_lt _ (by decide)
  have hrEq : r=427 := by omega
  have ht2048 : t%2048=427 := by simpa [r] using hrEq

  exact ht2048

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

/-- The q=0 and q=1 original-source parents of X_t are both
unreachable throughout t=427 (mod 2048).  The q=0 parent
descends through exact source inverses to the sum-seven fibre;
the q=1 parent lies in the arbitrary-depth dyadic inverse cone. -/
theorem blank_no_u5_q0_parent_t427 (t : Nat)
    (ht : t%2048=427) :
    ¬ CReach (64*t+5) (32*t+3) := by
  let n := t/128
  have htdiv : t%2048+2048*(t/2048)=t :=
    Nat.mod_add_div t 2048
  have hdecomp : t=2048*(t/2048)+427 := by omega
  have htnorm :
      t=128*(16*(t/2048)+3)+43 := by
    rw [hdecomp]
    ring
  have hmod128 : t%128=43 := by rw [htnorm]; omega
  have hdiv128 : t%128+128*(t/128)=t :=
    Nat.mod_add_div t 128
  have hnEq : n=16*(t/2048)+3 := by
    dsimp [n]
    omega
  have htEq : t=128*n+43 := by
    rw [hnEq]
    exact htnorm
  have hn16 : n%16=3 := by rw [hnEq]; omega
  have hn3 : 3≤n := by omega

  have hXnot : ¬ CReach (44*t-1) (42*t-1) := by
    intro hX
    obtain ⟨a,k,hprev,hstep⟩ :=
      BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
        (44*t-1) (42*t-1) (by omega) hX
    have hfan :=
      (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
        t a k (by omega)).mp hstep
    rcases hfan with
      ⟨q,U,hfanPow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
    have hnot16 : ¬ 16∣43*t-1 := by
      intro hd
      have hmod : (43*t-1)%16=0 :=
        Nat.mod_eq_zero_of_dvd hd
      rw [htEq] at hmod
      omega
    have hqle : q≤1 := by
      by_contra hq
      have hq2 : 2≤q := by omega
      have hdiv : 16∣4^q*U := by
        refine ⟨4^(q-2)*U,?_⟩
        have hpowq : 4^q=16*4^(q-2) := by
          rw [show q=(q-2)+2 by omega,Nat.pow_add]
          norm_num
        rw [hpowq]
        ring
      have hdiv' : 16∣43*t-1 := by
        rw [hfanPow]
        exact hdiv
      exact hnot16 hdiv'
    have hqcases : q=0 ∨ q=1 := by omega
    rcases hqcases with hq0 | hq1
    · subst q
      have hU : U=8*(688*n+231) := by
        norm_num at hfanPow
        rw [htEq] at hfanPow
        omega
      have ha0 : a=5504*n+1846 := by omega
      have hk0 : k=5440*n+1824 := by omega
      have hP0 : CReach (5504*n+1846) (5440*n+1824) := by
        simpa only [ha0,hk0] using hprev
      have hP1 : CReach (10944*n+3668) (2720*n+911) := by
        have hiff := BB6.Agent46.six_even_right_blank_reach_iff
          (5504*n+1846) (5440*n+1824)
          (by omega) (by omega) (by omega) (by omega)
        have hx : (5504*n+1846)+(5440*n+1824)-2=
            10944*n+3668 := by omega
        have hy : ((5440*n+1824)-2)/2=2720*n+911 := by omega
        simpa only [hx,hy] using hiff.mp hP0
      obtain ⟨a1,k1,hprev1,hstep1⟩ :=
        BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
          (10944*n+3668) (2720*n+911) (by omega) hP1
      have hform1 :=
        BB6.Agent46.section_evenodd_sum3_inverse
          a1 k1 (10944*n+3668) (2720*n+911)
          (by omega) (by omega) (by omega) hstep1
      have hP2 : CReach (6832*n+2287) (4776*n+1598) := by
        have hx :
            ((10944*n+3668)+(2720*n+911)-5)/2=
              6832*n+2287 := by omega
        have hy :
            ((10944*n+3668)+3*(2720*n+911)-9)/4=
              4776*n+1598 := by omega
        simpa only [hform1.1,hform1.2,hx,hy] using hprev1
      have hP3 : CReach (11608*n+3883) (2388*n+798) := by
        have hiff := BB6.Agent46.six_even_right_blank_reach_iff
          (6832*n+2287) (4776*n+1598)
          (by omega) (by omega) (by omega) (by omega)
        have hx : (6832*n+2287)+(4776*n+1598)-2=
            11608*n+3883 := by omega
        have hy : ((4776*n+1598)-2)/2=2388*n+798 := by omega
        simpa only [hx,hy] using hiff.mp hP2
      have hP4 : CReach (13996*n+4679) (1194*n+398) := by
        have hiff := BB6.Agent46.six_even_right_blank_reach_iff
          (11608*n+3883) (2388*n+798)
          (by omega) (by omega) (by omega) (by omega)
        have hx : (11608*n+3883)+(2388*n+798)-2=
            13996*n+4679 := by omega
        have hy : ((2388*n+798)-2)/2=1194*n+398 := by omega
        simpa only [hx,hy] using hiff.mp hP3
      obtain ⟨a4,k4,hprev4,hstep4⟩ :=
        BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
          (13996*n+4679) (1194*n+398) (by omega) hP4
      have hfiber :=
        (BB6.Agent20C70.seven_inverse_iff
          a4 k4 (13996*n+4679) (1194*n+398)
          (by omega) (by omega) (by omega)).mp hstep4
      rcases hfiber with ⟨ha4,hk4⟩ |
          ⟨ha3,haodd,hlow4,hsum4,hcost4⟩
      · have hD : CReach (15190*n+5075) (597*n+198) := by
          have hda : a4=15190*n+5075 := by rw [ha4]; omega
          have hdk : k4=597*n+198 := by omega
          simpa only [hda,hdk] using hprev4
        have hbad :=
          BB6.Agent11High.blank_no_odd_sum_two
            (15190*n+5075) (597*n+198)
            (by omega) (by omega) (by omega)
        exact hbad hD
      · have hA : a4=(15190*n+5066)/4 := by omega
        have hK : k4=(25173*n+8397)/4 := by omega
        have hE :
            CReach ((15190*n+5066)/4) ((25173*n+8397)/4) := by
          simpa only [hA,hK] using hprev4
        have hbad :=
          BB6.Agent11High.blank_no_odd_sum_two
            ((15190*n+5066)/4) ((25173*n+8397)/4)
            (by omega) (by omega) (by omega)
        exact hbad hE
    · subst q
      have hU : U=2*(688*n+231) := by
        norm_num at hfanPow
        rw [htEq] at hfanPow
        omega
      have ha1 : a=1376*n+460 := by omega
      have hk1 : k=7504*n+2514 := by omega
      let u := 1876*n+629
      have hu9 : 9≤u := by dsimp [u]; omega
      have hu4 : u%4=1 := by dsimp [u]; omega
      have hb : 7504*n+2514+2=2^2*u := by
        dsimp [u]
        omega
      have hmass :
          (1376*n+460+2*(7504*n+2514)+4*2)%8=0 := by
        omega
      have hnot :=
        BB6.Agent19SixCone.dyadic_six_cone_no_blank
          2 (1376*n+460) (7504*n+2514) u hu9 hu4 hb hmass
      exact hnot (by simpa only [ha1,hk1] using hprev)

  intro hparent
  exact hXnot (q0_parent_reach_implies_X t (by omega) hparent)

/-- The q=0 parent of the y=3 U5 terminal is excluded on the
w=1821 (mod 2048) cylinder by the two-depth source fan above. -/
theorem blank_no_u5_q0_parent_w1821 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%2048=1821) :
    ¬ CReach (8*(m+1)-3) (4*(m+1)-1) := by
  have htmod := u5_m8_t_mod2048_w1821 w s m t hs hm hp hw
  have hnot := blank_no_u5_q0_parent_t427 t htmod
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
unreachable on w=1821 (mod 2048): q=0 uses the exact nested
source fan and dyadic cone; q=1 uses the odd-right sum-two
invariant, and q>=2 contradicts p=1 (mod 8). -/
theorem blank_no_u5_residual_m8w_w1821 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%2048=1821) :
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
  have hwge : 1821≤w := by omega
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
            exact blank_no_u5_q0_parent_w1821 w s m t hs hm hp hw hparent0
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
unreachable on w=1821 (mod 2048). -/
theorem blank_no_u5_B_s_m8w_w1821 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%2048=1821) :
    ¬ CReach (54+90*s) (127+211*s) := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  intro hB
  have hterminal :=
    (BB6.Agent3U5M8.u5_residual_six_even_right_chain (8*w) s hs').mp hB
  have hM : 201+420*(8*w)=201+3360*w := by omega
  have hterminal' : CReach (302+512*s-4*(201+3360*w)) 3 := by
    simpa only [hM] using hterminal
  exact blank_no_u5_residual_m8w_w1821 w s m hs hm hw hterminal'

/-- Both exact source parents of A_s are excluded on
w=1821 (mod 2048). -/
theorem blank_no_u5_A_s_m8w_w1821 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%2048=1821) :
    ¬ CReach (130+208*s) (94+152*s) := by
  have hdiv : 8∣2^(201+3360*w) := by
    change 2^3∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod : (2^(201+3360*w))%8=0 := Nat.mod_eq_zero_of_dvd hdiv
  have hsmod : (211*s+129)%8=0 := by
    rw [hs,Nat.mul_mod,hpowmod]
  have hs8 : s%8=5 := by omega
  have hL := BB6.Agent11M0SumZeroVerified.blank_no_L_s_mod8_five s hs8
  have hB := blank_no_u5_B_s_m8w_w1821 w s m hs hm hw
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
w=1821 (mod 2048). -/
theorem blank_no_high_m0_u5_w1821 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%2048=1821) :
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
  exact blank_no_u5_A_s_m8w_w1821 w s m hs hm hw hA'

/-- Nonvacuity: every n supplies an actual residual solution and
an excluded authentic blank-root state in the w=1821 mod2048
subcylinder.  The existing residual monotonicity theorem makes
the resulting roots pairwise distinct. -/
theorem every_w1821_residual_has_unreachable_root (n : Nat) :
    ∃ s m,
      211*s+129=5*2^(201+3360*(2048*n+1821)) ∧
      32*s=32+840*(2048*n+1821)+m ∧
      (39+64*s)%32768=18791 ∧
      (1+2*s)%1024=587 ∧
      ¬ CReach (2*(39+64*s)+3) (3*(39+64*s)+7) := by
  obtain ⟨s,m,hs,hm,_,_⟩ :=
    BB6.Agent3U5M32W485HighStop.u5_residual_nonempty
      (2048*n+1821)
  have hw : (2048*n+1821)%2048=1821 := by omega
  have hroot := blank_no_high_m0_u5_w1821
    (2048*n+1821) s m hs hm hw
  have hres :=
    BB6.Agent3U5M32W485HighStop.u5_high_root_parameter_residue
      (2048*n+1821) s hs
  exact ⟨s,m,hs,hm,hres.1,hres.2,hroot⟩

/-- The excluded roots on distinct w parameters are strictly
increasing, hence this source-excluded cylinder is infinite. -/
theorem w1821_roots_pairwise_distinct
    (n1 n2 s1 s2 : Nat)
    (hn : n1<n2)
    (hs1 : 211*s1+129=5*2^(201+3360*(2048*n1+1821)))
    (hs2 : 211*s2+129=5*2^(201+3360*(2048*n2+1821))) :
    39+64*s1 < 39+64*s2 := by
  have hw : 2048*n1+1821 < 2048*n2+1821 := by omega
  have hslt :=
    BB6.Agent3U5M32W485HighStop.u5_residual_s_strict_mono
      (2048*n1+1821) (2048*n2+1821) s1 s2 hw hs1 hs2
  omega

#print axioms u5_m8_t_mod2048_w1821
#print axioms blank_no_u5_q0_parent_t2475
#print axioms blank_no_u5_q0_parent_w1821
#print axioms blank_no_u5_residual_m8w_w1821
#print axioms blank_no_u5_B_s_m8w_w1821
#print axioms blank_no_u5_A_s_m8w_w1821
#print axioms blank_no_high_m0_u5_w1821
#print axioms every_w1821_residual_has_unreachable_root
#print axioms w1821_roots_pairwise_distinct

end BB6.Agent3U5Q0W1821HighStop

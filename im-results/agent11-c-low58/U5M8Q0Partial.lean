import OddOddLowVal
import EvenOddFourExact
import HighSumTwo
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11U5M8Q0Partial
open BB6.Agent3

/-- The q=0 residual parent for t=5 (mod 8) is blank-unreachable:
    its exact odd/odd low-value parent has odd right coordinate and
    coordinate sum 1 (mod 4), forbidden by the source blank-image invariant. -/
theorem blank_no_u5_q0_t5 (u : Nat) :
    ¬ CReach (352*u+219) (336*u+209) := by
  intro h
  have hA : CReach (344*u+212) (340*u+209) := by
    have hiff := (oddodd_lowval_blank_reach_iff
      (352*u+219) (336*u+209)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp h
    have hx : ((352*u+219)+(336*u+209)-4)/2=344*u+212 := by omega
    have hy : ((352*u+219)+3*(336*u+209)-10)/4=340*u+209 := by omega
    simpa only [hx,hy] using hiff
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    (344*u+212) (340*u+209)
    (by omega) (by omega) (by omega) (by omega) hA

/-- The residual equation fixes the parameter t in p=m+1=8*t+1:
    t+w is divisible by eight. The proof uses the exact affine identity,
    reduced modulo 64 (the right side has 2-adic valuation at least six). -/
theorem u5_m8_t_plus_w_mod8 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1) :
    (t+w)%8=0 := by
  have hid :
      211*(m+1)+10669+22155*(8*w)=160*2^(201+3360*w) := by
    omega
  have hdiv : 64∣2^(201+3360*w) := by
    change 2^6∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod : (2^(201+3360*w))%64=0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  rw [hp] at hid
  have hmod :
      (211*(8*t+1)+10669+22155*(8*w))%64=0 := by
    rw [hid]
    simp [Nat.mul_mod,hpowmod]
  have hlin :
      211*(8*t+1)+10669+22155*(8*w)=
        64*(26*t+170+2769*w)+24*(t+w) := by
    omega
  rw [hlin] at hmod
  omega

/-- q=0 parent reachability forces two exact inverse edges, ending at
    X=(44*t-1,42*t-1). -/
private theorem q0_parent_reach_implies_X (t : Nat) (ht : 1≤t)
    (h : CReach (64*t+5) (32*t+3)) :
    CReach (44*t-1) (42*t-1) := by
  have h1 := (oddodd_val3_blank_reach_iff
    (64*t+5) (32*t+3)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h
  have h1' : CReach (48*t+2) (40*t+1) := by
    have hx : ((64*t+5)+(32*t+3)-4)/2=48*t+2 := by omega
    have hy : ((64*t+5)+3*(32*t+3)-10)/4=40*t+1 := by omega
    simpa only [hx,hy] using h1
  have h2 := (evenodd_four_blank_reach_iff
    (48*t+2) (40*t+1)
    (by omega) (by omega) (by omega) (by omega)).mp h1'
  have h2' : CReach (44*t-1) (42*t-1) := by
    have hx : ((48*t+2)+(40*t+1)-5)/2=44*t-1 := by omega
    have hy : ((48*t+2)+3*(40*t+1)-9)/4=42*t-1 := by omega
    simpa only [hx,hy] using h2
  exact h2'

/-- The q=0 parent is excluded for even w: t is even, so X has odd
    right counter and coordinate sum 2 modulo four. -/
theorem blank_no_u5_q0_parent_w_even (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1) (hw : w%2=0) (ht : 1≤t) :
    ¬ CReach (8*(m+1)-3) (4*(m+1)-1) := by
  have htw := u5_m8_t_plus_w_mod8 w s m t hs hm hp
  have htEven : t%2=0 := by omega
  have hX : ¬ CReach (44*t-1) (42*t-1) := by
    apply BB6.Agent11High.blank_no_odd_sum_two
    · omega
    · omega
    · omega
  intro h
  have hpull : CReach (64*t+5) (32*t+3) := by
    have hx : 8*(m+1)-3=64*t+5 := by omega
    have hy : 4*(m+1)-1=32*t+3 := by omega
    simpa only [hx,hy] using h
  exact hX (q0_parent_reach_implies_X t ht hpull)

/-- The q=0 parent is also excluded for w=3 (mod 8): then t=5
    (mod 8), and the next odd/odd low-value parent has sum 1 (mod 4). -/
theorem blank_no_u5_q0_parent_w3 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1) (hw : w%8=3) (ht : 1≤t) :
    ¬ CReach (8*(m+1)-3) (4*(m+1)-1) := by
  have htw := u5_m8_t_plus_w_mod8 w s m t hs hm hp
  have ht5 : t%8=5 := by omega
  have htEq : t=8*(t/8)+5 := by omega
  have hX : ¬ CReach (44*t-1) (42*t-1) := by
    have hbase := blank_no_u5_q0_t5 (t/8)
    have hx : 352*(t/8)+219=44*t-1 := by rw [htEq]; omega
    have hy : 336*(t/8)+209=42*t-1 := by rw [htEq]; omega
    simpa only [hx,hy] using hbase
  intro h
  have hpull : CReach (64*t+5) (32*t+3) := by
    have hx : 8*(m+1)-3=64*t+5 := by omega
    have hy : 4*(m+1)-1=32*t+3 := by omega
    simpa only [hx,hy] using h
  exact hX (q0_parent_reach_implies_X t ht hpull)

/- The remaining q=0 cases w=1,5,7 (mod 8) are not covered here. -/

#print axioms u5_m8_t_plus_w_mod8
#print axioms blank_no_u5_q0_t5
#print axioms blank_no_u5_q0_parent_w_even
#print axioms blank_no_u5_q0_parent_w3
end BB6.Agent11U5M8Q0Partial

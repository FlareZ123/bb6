import P1SecondReach
namespace BB6.P1SecondPairs
open BB6.Agent1

private theorem base_G (w : Nat) :
    G (12*w) (40*w+9) = (48*w+4,16*w+7) := by
  have hn : ¬ 40*w+9 < 2*(12*w) := by omega
  have hm : ¬ 40*w+9 ≤ 2*(12*w)+1 := by omega
  rw [G]
  simp [hn,hm]
  omega

private theorem nested_G (w : Nat) (hw : 1≤w) :
    G (22*w+2) (20*w+3) = (48*w+4,16*w+7) := by
  have hl : 20*w+3 < 2*(22*w+2) := by omega
  have hk : 22*w+2 - ((20*w+3)/2+1) = 12*w := by omega
  have hc : 2*(20*w+3)+3=40*w+9 := by omega
  rw [G]
  simp only [hl,dite_true]
  rw [hk,hc]
  exact base_G w

theorem first_two_steps (w : Nat) (hw : 1≤w) :
    T (24*w-4) (40*w+13)=some (24*w-1,40*w+11) ∧
    T (24*w-1) (40*w+11)=some (48*w+4,16*w+7) := by
  constructor
  · have hc0 : 40*w+13≠0 := by omega
    have hc1 : 40*w+13≠1 := by omega
    have ha : (24*w-4)%2=0 := by omega
    unfold T
    simp [hc1,ha]
    omega
  · have hc0 : 40*w+11≠0 := by omega
    have hc1 : 40*w+11≠1 := by omega
    have ha : (24*w-1)%2≠0 := by omega
    have hc2 : 40*w+11≠2 := by omega
    have hc3 : 40*w+11≠3 := by omega
    have hb : (24*w-1)/2+1=12*w := by omega
    have hd : (40*w+11)-2=40*w+9 := by omega
    unfold T
    simp [hc1,ha,hc2,hc3,hb,hd,base_G]

theorem second_two_steps (w : Nat) (hw : 1≤w) :
    T (44*w) (20*w+7)=some (44*w+3,20*w+5) ∧
    T (44*w+3) (20*w+5)=some (48*w+4,16*w+7) := by
  constructor
  · have hc0 : 20*w+7≠0 := by omega
    have hc1 : 20*w+7≠1 := by omega
    have ha : (44*w)%2=0 := by omega
    unfold T
    simp [hc1,ha]
  · have hc0 : 20*w+5≠0 := by omega
    have hc1 : 20*w+5≠1 := by omega
    have ha : (44*w+3)%2≠0 := by omega
    have hc2 : 20*w+5≠2 := by omega
    have hc3 : 20*w+5≠3 := by omega
    have hb : (44*w+3)/2+1=22*w+2 := by omega
    have hd : (20*w+5)-2=20*w+3 := by omega
    unfold T
    simp [hc1,ha,hc2,hc3,hb,hd,nested_G w hw]

theorem first_reaches_second (w : Nat) (hw : 1≤w)
    (hr : Reach (24*w-4) (40*w+13)) :
    Reach (48*w+4) (16*w+7) := by
  obtain ⟨h1,h2⟩ := first_two_steps w hw
  exact Reach.next (24*w-1) (40*w+11) (48*w+4) (16*w+7)
    (Reach.next (24*w-4) (40*w+13) (24*w-1) (40*w+11) hr h1) h2

theorem second_reaches_second (w : Nat) (hw : 1≤w)
    (hr : Reach (44*w) (20*w+7)) :
    Reach (48*w+4) (16*w+7) := by
  obtain ⟨h1,h2⟩ := second_two_steps w hw
  exact Reach.next (44*w+3) (20*w+5) (48*w+4) (16*w+7)
    (Reach.next (44*w) (20*w+7) (44*w+3) (20*w+5) hr h1) h2

/-- A genuine iff for the whole second critical feeder whenever q is odd. -/
theorem odd_second_iff_two (q : Nat) (hq : 1≤q) (hodd : q%2=1) :
    Reach (6*BB6.Agent45TwoRoot.u2 q-2) (2*BB6.Agent45TwoRoot.u2 q+5) ↔
    Reach (24*BB6.P1SecondFan.w2 q-4) (40*BB6.P1SecondFan.w2 q+13) ∨
    Reach (44*BB6.P1SecondFan.w2 q) (20*BB6.P1SecondFan.w2 q+7) := by
  constructor
  · exact BB6.P1SecondFan.odd_second_reach_requires_two q hq hodd
  · intro h
    have hre := BB6.P1SecondFan.odd_w2_identity q hq hodd
    have hpositive : 1≤BB6.P1SecondFan.w2 q := by
      have hu : 3 ≤ BB6.Agent45TwoRoot.u2 q := by
        simpa only [BB6.Agent45TwoRoot.u2] using
          BB6.P1DualValuation.feeder_u_lower q hq
      omega
    have hb : 6*BB6.Agent45TwoRoot.u2 q-2 =
        48*BB6.P1SecondFan.w2 q+4 := by omega
    have hd : 2*BB6.Agent45TwoRoot.u2 q+5 =
        16*BB6.P1SecondFan.w2 q+7 := by omega
    rw [hb,hd]
    rcases h with ha | hb'
    · exact first_reaches_second (BB6.P1SecondFan.w2 q) hpositive ha
    · exact second_reaches_second (BB6.P1SecondFan.w2 q) hpositive hb'

/-- Exact three-line iff for every odd-q original P1 critical reset. -/
theorem odd_critical_iff_three (q : Nat) (hq : 1≤q) (hodd : q%2=1) :
    Reach 2 (14*2^(16*q+2)-2*(16*q+2)-10) ↔
    Reach (4*BB6.Agent45TwoRoot.u2 q-4) (4*BB6.Agent45TwoRoot.u2 q+9) ∨
    Reach (24*BB6.P1SecondFan.w2 q-4) (40*BB6.P1SecondFan.w2 q+13) ∨
    Reach (44*BB6.P1SecondFan.w2 q) (20*BB6.P1SecondFan.w2 q+7) := by
  rw [BB6.Agent45TwoRoot.two_sector_critical_iff_feeders q hq,
    odd_second_iff_two q hq hodd]

#print axioms odd_critical_iff_three
#print axioms odd_second_iff_two
#print axioms first_reaches_second
#print axioms second_reaches_second
#print axioms first_two_steps
#print axioms second_two_steps
end BB6.P1SecondPairs

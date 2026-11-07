import C70Root
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20C70
open BB6.Agent46

/-- Two-parameter lift of the exact two-source 70-cylinder fibre. -/
theorem rect70_fibre (s t a k : Nat)
    (h : secNext (a,k)=some (128*s+1,128*t+70)) :
    (a=128*s+128*t+69 ∧ k=64*t+34) ∨
    (a=32*s+32*t+15 ∧ k=48*s+112*t+58) := by
  rcases seven_inverse a k (128*s+1) (128*t+70)
    (by omega) (by omega) (by omega) h with hd | ho
  · exact Or.inl (by constructor <;> omega)
  · exact Or.inr (by constructor <;> omega)

/-- The direct source of the two-dimensional rectangle has two parents. -/
theorem rect70_second_fibre (s t a k : Nat)
    (h : secNext (a,k)=some (128*s+128*t+69,64*t+34)) :
    (a=128*s+192*t+101 ∧ k=32*t+16) ∨
    (a=32*s+48*t+23 ∧ k=48*s+104*t+52) := by
  rcases seven_inverse a k (128*s+128*t+69) (64*t+34)
    (by omega) (by omega) (by omega) h with hd | ho
  · exact Or.inl (by constructor <;> omega)
  · exact Or.inr (by constructor <;> omega)

private theorem rect70_forced_odd (s t : Nat) :
    BB6.Agent3.CReach (32*s+32*t+15) (48*s+112*t+58) →
    BB6.Agent3.CReach (80*s+144*t+71) (24*s+56*t+28) := by
  intro hr
  have h := (six_even_right_blank_reach_iff
    (32*s+32*t+15) (48*s+112*t+58)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hx : (32*s+32*t+15)+(48*s+112*t+58)-2=
      80*s+144*t+71 := by omega
  have hy : ((48*s+112*t+58)-2)/2=24*s+56*t+28 := by omega
  rw [hx,hy] at h
  exact h

private theorem rect70_forced_odd_second (s t : Nat) :
    BB6.Agent3.CReach (80*s+144*t+71) (24*s+56*t+28) →
    BB6.Agent3.CReach (104*s+200*t+97) (12*s+28*t+13) := by
  intro hr
  have h := (six_even_right_blank_reach_iff
    (80*s+144*t+71) (24*s+56*t+28)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hx : (80*s+144*t+71)+(24*s+56*t+28)-2=
      104*s+200*t+97 := by omega
  have hy : ((24*s+56*t+28)-2)/2=12*s+28*t+13 := by omega
  rw [hx,hy] at h
  exact h

private theorem rect70_forced_direct (s t : Nat) :
    BB6.Agent3.CReach (128*s+192*t+101) (32*t+16) →
    BB6.Agent3.CReach (128*s+224*t+115) (16*t+7) := by
  intro hr
  have h := (six_even_right_blank_reach_iff
    (128*s+192*t+101) (32*t+16)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hx : (128*s+192*t+101)+(32*t+16)-2=
      128*s+224*t+115 := by omega
  have hy : ((32*t+16)-2)/2=16*t+7 := by omega
  rw [hx,hy] at h
  exact h

private theorem rect70_forced_other (s t : Nat) :
    BB6.Agent3.CReach (32*s+48*t+23) (48*s+104*t+52) →
    BB6.Agent3.CReach (80*s+152*t+73) (24*s+52*t+25) := by
  intro hr
  have h := (six_even_right_blank_reach_iff
    (32*s+48*t+23) (48*s+104*t+52)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hx : (32*s+48*t+23)+(48*s+104*t+52)-2=
      80*s+152*t+73 := by omega
  have hy : ((48*s+104*t+52)-2)/2=24*s+52*t+25 := by omega
  rw [hx,hy] at h
  exact h

/-- Source-exact two-dimensional rectangle of absent blank-section states.
    Covers all counters with left 1(mod128) and right 70(mod128),
    without restrictions on the quotient indices. -/
theorem blank_no_rect_1_70_mod128 (s t : Nat) :
    ¬ BB6.Agent3.CReach (128*s+1) (128*t+70) := by
  intro hr
  obtain hDirect | hOdd := reach_parent_two
    (128*s+1) (128*t+70)
    (128*s+128*t+69) (64*t+34)
    (32*s+32*t+15) (48*s+112*t+58)
    (by omega) (rect70_fibre s t) hr
  · obtain hDir2 | hOdd2 := reach_parent_two
      (128*s+128*t+69) (64*t+34)
      (128*s+192*t+101) (32*t+16)
      (32*s+48*t+23) (48*s+104*t+52)
      (by omega) (rect70_second_fibre s t) hDirect
    · exact odd_sum_two_unreachable (128*s+224*t+115) (16*t+7)
        (by omega) (by omega) (by omega)
        (rect70_forced_direct s t hDir2)
    · exact odd_sum_two_unreachable (80*s+152*t+73) (24*s+52*t+25)
        (by omega) (by omega) (by omega)
        (rect70_forced_other s t hOdd2)
  · exact odd_sum_two_unreachable (104*s+200*t+97) (12*s+28*t+13)
      (by omega) (by omega) (by omega)
      (rect70_forced_odd_second s t (rect70_forced_odd s t hOdd))

/-- Two genuinely high-gate parameter cylinders transport to the
    absent 1/70 modulo-128 rectangle, at every unbounded stopping depth. -/
theorem blank_no_high_63_82_or_127_18 (j m k : Nat)
    (hres : (j%128=63 ∧ m%128=82) ∨ (j%128=127 ∧ m%128=18))
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  have hm : 3≤m := by omega
  have hdiv : 128 ∣ (2:Nat)^(2*m+2) := by
    change (2:Nat)^7 ∣ (2:Nat)^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hdiv
  have hprod : 128 ∣ 2^(2*m+2)*(j+3) := by
    refine ⟨w*(j+3),?_⟩
    rw [hw]
    ac_rfl
  have hmod : (k+j+3*m+5)%128=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hprod
  have hjmod : (2*j+3)%128=1 := by omega
  have hkmod : k%128=70 := by omega
  have hj : 2*j+3=128*((2*j+3)/128)+1 := by omega
  have hk : k=128*(k/128)+70 := by omega
  intro hr
  rw [hj,hk] at hr
  exact blank_no_rect_1_70_mod128 ((2*j+3)/128) (k/128) hr

#print axioms blank_no_high_63_82_or_127_18

#print axioms blank_no_rect_1_70_mod128
end BB6.Agent20C70

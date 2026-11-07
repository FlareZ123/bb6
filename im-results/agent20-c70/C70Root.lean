import SevenInverse
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20C70
open BB6.Agent46

/-- Exact two-parent source fibre of the 70(mod128) low-counter cylinder. -/
theorem low70_fibre (q a k : Nat)
    (h : secNext (a,k) = some (1,128*q+70)) :
    (a=128*q+69 ∧ k=64*q+34) ∨
    (a=32*q+15 ∧ k=112*q+58) := by
  obtain hdir | hodd := seven_inverse a k 1 (128*q+70)
    (by omega) (by omega) (by omega) h
  · left
    constructor <;> omega
  · right
    constructor <;> omega

/-- The direct precursor of the low ray has precisely two source fibres. -/
theorem high70_fibre (q a k : Nat)
    (h : secNext (a,k) = some (128*q+69,64*q+34)) :
    (a=192*q+101 ∧ k=32*q+16) ∨
    (a=48*q+23 ∧ k=104*q+52) := by
  obtain hdir | hodd := seven_inverse a k (128*q+69) (64*q+34)
    (by omega) (by omega) (by omega) h
  · left
    constructor <;> omega
  · right
    constructor <;> omega

private theorem reach_parent_two (x y u v w z : Nat) (hx : x≠5)
    (hpar : ∀ a k, secNext (a,k)=some (x,y) →
      (a=u ∧ k=v) ∨ (a=w ∧ k=z))
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach u v ∨ BB6.Agent3.CReach w z := by
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          rcases hpar a k hedge with ⟨ha,hk⟩ | ⟨ha,hk⟩
          · left
            refine ⟨n,?_⟩
            simpa only [ha,hk] using hp
          · right
            refine ⟨n,?_⟩
            simpa only [ha,hk] using hp

private theorem direct_112 (q : Nat) :
    BB6.Agent3.CReach (32*q+15) (112*q+58) →
    BB6.Agent3.CReach (144*q+71) (56*q+28) := by
  intro hr
  have h := (six_even_right_blank_reach_iff
    (32*q+15) (112*q+58) (by omega) (by omega)
    (by omega) (by omega)).mp hr
  have hx : (32*q+15)+(112*q+58)-2=144*q+71 := by omega
  have hy : ((112*q+58)-2)/2=56*q+28 := by omega
  rw [hx,hy] at h
  exact h

private theorem direct_56 (q : Nat) :
    BB6.Agent3.CReach (144*q+71) (56*q+28) →
    BB6.Agent3.CReach (200*q+97) (28*q+13) := by
  intro hr
  have h := (six_even_right_blank_reach_iff
    (144*q+71) (56*q+28) (by omega) (by omega)
    (by omega) (by omega)).mp hr
  have hx : (144*q+71)+(56*q+28)-2=200*q+97 := by omega
  have hy : ((56*q+28)-2)/2=28*q+13 := by omega
  rw [hx,hy] at h
  exact h

private theorem direct_104 (q : Nat) :
    BB6.Agent3.CReach (48*q+23) (104*q+52) →
    BB6.Agent3.CReach (152*q+73) (52*q+25) := by
  intro hr
  have h := (six_even_right_blank_reach_iff
    (48*q+23) (104*q+52) (by omega) (by omega)
    (by omega) (by omega)).mp hr
  have hx : (48*q+23)+(104*q+52)-2=152*q+73 := by omega
  have hy : ((104*q+52)-2)/2=52*q+25 := by omega
  rw [hx,hy] at h
  exact h

private theorem direct_32 (q : Nat) :
    BB6.Agent3.CReach (192*q+101) (32*q+16) →
    BB6.Agent3.CReach (224*q+115) (16*q+7) := by
  intro hr
  have h := (six_even_right_blank_reach_iff
    (192*q+101) (32*q+16) (by omega) (by omega)
    (by omega) (by omega)).mp hr
  have hx : (192*q+101)+(32*q+16)-2=224*q+115 := by omega
  have hy : ((32*q+16)-2)/2=16*q+7 := by omega
  rw [hx,hy] at h
  exact h

private theorem odd_sum_two_unreachable (x y : Nat)
    (hy : 5≤y) (ho : y%2=1) (hs : (x+y)%4=2) :
    ¬BB6.Agent3.CReach x y := by
  rintro ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      have h := BB6.Agent3.blank_section_odd_image n x y ht hy ho
      omega

/-- A source-exact three-layer finite reverse tree, independent of q.
    All leaves have odd right counter >=7 and coordinate sum 2 mod4. -/
theorem blank_no_one_70_mod128 (q : Nat) :
    ¬ BB6.Agent3.CReach 1 (128*q+70) := by
  intro hr
  obtain h1 | h2 := reach_parent_two 1 (128*q+70)
    (128*q+69) (64*q+34) (32*q+15) (112*q+58)
    (by omega) (low70_fibre q) hr
  · obtain h3 | h4 := reach_parent_two (128*q+69) (64*q+34)
      (192*q+101) (32*q+16) (48*q+23) (104*q+52)
      (by omega) (high70_fibre q) h1
    · exact odd_sum_two_unreachable (224*q+115) (16*q+7)
        (by omega) (by omega) (by omega) (direct_32 q h3)
    · exact odd_sum_two_unreachable (152*q+73) (52*q+25)
        (by omega) (by omega) (by omega) (direct_104 q h4)
  · exact odd_sum_two_unreachable (200*q+97) (28*q+13)
      (by omega) (by omega) (by omega) (direct_56 q (direct_112 q h2))

/-- Every authentic low stopping parameter congruent 18 modulo 128
    lies in the newly forbidden right-counter cylinder. -/
theorem blank_no_low_depth_18_mod128 (m k : Nat)
    (hm : m%128=18) (hgate : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hdiv : 128 ∣ (2:Nat)^(2*m+3) := by
    change (2:Nat)^7 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hdiv
  have hkmod : k%128=70 := by
    rw [hw] at hgate
    omega
  have hk : k=128*(k/128)+70 := by omega
  intro hr
  rw [hk] at hr
  exact blank_no_one_70_mod128 (k/128) hr

#print axioms blank_no_low_depth_18_mod128

#print axioms blank_no_one_70_mod128
end BB6.Agent20C70

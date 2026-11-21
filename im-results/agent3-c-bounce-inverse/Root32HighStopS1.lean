import Root32HighStopIntegrated
import EvenEvenParentFan
import EvenRightUnique
import M0EvenEvenSumZero
import U5B2Root32
import Agent3CImage
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3Root32HighStopS1
open BB6.Agent46
open BB6.Agent3Root32HighStopIntegrated

/-- Odd-right blank images have sum residue zero or three modulo four;
this run-level form excludes the residue-one family. -/
theorem run_no_odd_sum_one (x y : Nat)
    (hx : 5<x) (hy : 5≤y) (ho : y%2=1)
    (hsum : (x+y)%4=1) : ¬ RunReach x y := by
  intro hr
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    have hi := BB6.Agent3.blank_section_odd_image n x y ht hy ho
    omega

/-- A genuine even-right target has its unique direct source parent,
transporting blank reachability one step backwards. -/
theorem run_evenright_parent (x y : Nat)
    (hx : 5<x) (hy6 : 6≤y) (hye : y%2=0)
    (hzero : (x+y)%8≠0) (hseven : (x+y)%8≠7)
    (hr : RunReach x y) :
    RunReach (x+y-2) ((y-2)/2) := by
  obtain ⟨a,k,hprev,hstep⟩ := run_parent_of_left_gt5 x y hx hr
  obtain ⟨ha,hk⟩ :=
    (BB6.Agent15.section_even_right_iff_affine a k x y hy6 hye hzero hseven).mp hstep
  simpa only [ha,hk] using hprev

/-- A power of two cannot equal 2^11 times an odd factor greater than
one. This elementary valuation gate removes the a=0 S1 parent. -/
theorem no_pow_two_times_odd_gt_one (v n : Nat)
    (hodd : v%2=1) (hgt : 1<v)
    (heq : 2^11*v=2^(n+3)) : False := by
  have hdiv : 2^11 ∣ 2^(n+3) := ⟨v,heq.symm⟩
  have hn : 11≤n+3 :=
    (Nat.pow_dvd_pow_iff_le_right (by decide : 1<2)).mp hdiv
  have hfactor : 2^(n+3)=2^11*2^(n+3-11) := by
    calc
      2^(n+3)=2^(11+(n+3-11)) := by congr 1 <;> omega
      _=2^11*2^(n+3-11) := by rw [Nat.pow_add]
  have hvEq : v=2^(n+3-11) := by
    apply Nat.mul_left_cancel (by decide : 0<2^11)
    calc
      2^11*v=2^(n+3) := heq
      _=2^11*2^(n+3-11) := hfactor
  by_cases hz : n+3-11=0
  · rw [hz] at hvEq
    simp at hvEq
    omega
  · have hpos : 1≤n+3-11 := by omega
    have hdiv2 : 2∣2^(n+3-11) := by
      have h : 2^1∣2^(n+3-11) := Nat.pow_dvd_pow 2 hpos
      simpa using h
    have heven : v%2=0 := by rw [hvEq]; exact Nat.mod_eq_zero_of_dvd hdiv2
    omega

/-- Exact S1 sum and cost identities, isolated from reachability data. -/
theorem s1_sum_cost_identities (u : Nat) :
    (352256*u+23690)+(348160*u+23414)=700416*u+47104 ∧
    (352256*u+23690)+2*(348160*u+23414)=1048576*u+70518 := by
  constructor <;> omega

/-- The S1 sum has exact 2-adic valuation eleven. -/
theorem s1_sum_valuation (u : Nat) :
    (352256*u+23690)+(348160*u+23414)=2^11*(342*u+23) := by omega

/-- The odd quotient in the S1 sum is always greater than one. -/
theorem s1_odd_quotient_facts (u : Nat) :
    (342*u+23)%2=1 ∧ 1<342*u+23 := by omega

/-- The valuation-eleven sum forces every even-a bounce depth in the
S1 fan to be at most nine. -/
theorem s1_bounce_depth_le_nine (u a n : Nat)
    (hnodd : n%2=1)
    (hxy : (352256*u+23690)+(348160*u+23414)=2^(n+1)*(a+2)) :
    n≤9 := by
  have hsumEq :
      (352256*u+23690)+(348160*u+23414)=2^11*(342*u+23) := by omega
  by_cases hnle : n≤9
  · exact hnle
  · have hn11 : 11≤n := by omega
    have hdivPow : 2^12∣2^(n+1) :=
      (Nat.pow_dvd_pow_iff_le_right (by decide : 1<2)).2 (by omega)
    rcases hdivPow with ⟨c,hc⟩
    have hsumDiv : 2^12∣(352256*u+23690)+(348160*u+23414) := by
      refine ⟨c*(a+2),?_⟩
      calc
        (352256*u+23690)+(348160*u+23414)=2^(n+1)*(a+2) := hxy
        _=(2^12*c)*(a+2) := by rw [hc]
        _=2^12*(c*(a+2)) := by ac_rfl
    rcases hsumDiv with ⟨d,hd⟩
    have hpow12 : 2^12=2^11*2 := by decide
    have hmul : 2^11*(342*u+23)=2^11*(2*d) := by
      calc
        2^11*(342*u+23)=
            (352256*u+23690)+(348160*u+23414) := hsumEq.symm
        _=2^12*d := hd
        _=2^11*(2*d) := by rw [hpow12]; ac_rfl
    have hVeq : 342*u+23=2*d :=
      Nat.mul_left_cancel (by decide : 0<2^11) hmul
    have hVeven : (342*u+23)%2=0 := by rw [hVeq]; simp
    omega

/-- The five possible odd-depth bounce parents of S1, with exact
coordinates. -/
theorem s1_bounce_parent_cases (u a k n : Nat)
    (hnodd : n%2=1) (hnle : n≤9)
    (hxy : (352256*u+23690)+(348160*u+23414)=2^(n+1)*(a+2))
    (hcost : 2*k+a+7+3*n=(352256*u+23690)+2*(348160*u+23414)) :
    (a=175104*u+11774 ∧ k=436736*u+29367) ∨
    (a=43776*u+2942 ∧ k=502400*u+33780) ∨
    (a=10944*u+734 ∧ k=518816*u+34881) ∨
    (a=2736*u+182 ∧ k=522920*u+35154) ∨
    (a=684*u+44 ∧ k=523946*u+35220) := by
  have hdepth : n=1 ∨ n=3 ∨ n=5 ∨ n=7 ∨ n=9 := by omega
  rcases s1_sum_cost_identities u with ⟨hsumEq,hcostEq⟩
  rw [hsumEq] at hxy
  rw [hcostEq] at hcost
  rcases hdepth with hn | hn | hn | hn | hn
  · subst n
    left
    constructor <;> omega
  · subst n
    right; left
    constructor <;> omega
  · subst n
    right; right; left
    constructor <;> omega
  · subst n
    right; right; right; left
    constructor <;> omega
  · subst n
    right; right; right; right
    constructor <;> omega

/-- Direct S1 source-parent coordinates. -/
theorem s1_direct_parent_coordinates (u a k : Nat)
    (ha : a=(352256*u+23690)+(348160*u+23414)-2)
    (hk : k=(348160*u+23414-2)/2) :
    a=700416*u+47102 ∧ k=174080*u+11706 := by
  constructor <;> omega

/-- Arithmetic facts for the two even-right exceptional parents. -/
theorem s1_p1_odd_sum_one_facts (u : Nat) :
    5<175104*u+11774 ∧ 5≤436736*u+29367 ∧
    (436736*u+29367)%2=1 ∧
    (175104*u+11774+436736*u+29367)%4=1 := by
  constructor <;> omega

theorem s1_p3_evenright_facts (u : Nat) :
    5<43776*u+2942 ∧ 6≤502400*u+33780 ∧
    (502400*u+33780)%2=0 ∧
    ((43776*u+2942)+(502400*u+33780))%8≠0 ∧
    ((43776*u+2942)+(502400*u+33780))%8≠7 := by
  constructor <;> omega

theorem s1_p3_parent_sum_one (u : Nat) :
    ((546176*u+36720)+(251200*u+16889))%4=1 := by omega

theorem s1_p9_evenright_facts (u : Nat) (hu8 : u%8=2) :
    5<684*u+44 ∧ 6≤523946*u+35220 ∧
    (523946*u+35220)%2=0 ∧
    ((684*u+44)+(523946*u+35220))%8≠0 ∧
    ((684*u+44)+(523946*u+35220))%8≠7 := by
  constructor <;> omega

theorem s1_p9_parent_sum_one (u : Nat) (hu4 : u%4=2) :
    ((524630*u+35262)+(261973*u+17609))%4=1 := by omega

/-- Parent-image facts after the n=1 S1 bounce. -/
theorem s1_p1_parent_facts (u a k : Nat)
    (haEq : a=175104*u+11774) (hkEq : k=436736*u+29367) :
    5<a ∧ 5≤k ∧ k%2=1 ∧ (a+k)%4=1 := by
  constructor <;> omega

/-- The n=3 even-right parent has an odd-right residue-one image. -/
theorem s1_p3d_odd_sum_one_facts (u : Nat) :
    5<546176*u+36720 ∧ 5≤251200*u+16889 ∧
    (251200*u+16889)%2=1 ∧
    ((546176*u+36720)+(251200*u+16889))%4=1 := by
  constructor <;> omega

/-- The n=9 even-right parent has an odd-right residue-one image. -/
theorem s1_p9d_odd_sum_one_facts (u : Nat) (hu4 : u%4=2) :
    5<524630*u+35262 ∧ 5≤261973*u+17609 ∧
    (261973*u+17609)%2=1 ∧
    ((524630*u+35262)+(261973*u+17609))%4=1 := by
  constructor <;> omega

/-- Exact coordinates of the n=3 even-right parent. -/
theorem s1_p3_evenright_coordinates (u : Nat) :
    (43776*u+2942)+(502400*u+33780)-2=546176*u+36720 ∧
    (502400*u+33780-2)/2=251200*u+16889 := by
  constructor <;> omega

/-- Exact coordinates of the n=9 even-right parent. -/
theorem s1_p9_evenright_coordinates (u : Nat) :
    (684*u+44)+(523946*u+35220)-2=524630*u+35262 ∧
    (523946*u+35220-2)/2=261973*u+17609 := by
  constructor <;> omega

/-- Exact-root B0 exclusion, converted to the explicit run predicate. -/
theorem root32_b0_unreachable (r E u : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    ¬ RunReach (10944*u+734) (518816*u+34881) := by
  have hB0C := BB6.Agent3U5B2Root32.blank_no_b2_root32_from_exact_root_index
    r E u hr64 hE hRoot
  intro h
  rcases h with ⟨n,hn⟩
  have hC : BB6.Agent3.CReach (734+10944*u) (34881+518816*u) := by
    change ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (734+10944*u,34881+518816*u)
    refine ⟨n,?_⟩
    simpa [Nat.add_comm] using hn
  exact hB0C hC

/-- The exact root32 equation supplies u=1802+6720*t, hence u=2 mod 8.
Under this root hypothesis the complete S1 source fan has only D0 and
P7 left. The P7 branch is deliberately not claimed closed here. -/
theorem S1_reach_implies_D0_or_P7 (u : Nat)
    (hu8 : u%8=2)
    (hB0 : ¬ RunReach (10944*u+734) (518816*u+34881))
    (hS1 : RunReach (352256*u+23690) (348160*u+23414)) :
    RunReach (700416*u+47102) (174080*u+11706) ∨
    RunReach (2736*u+182) (522920*u+35154) := by
  obtain ⟨a,k,hprev,hstep⟩ := run_parent_of_left_gt5
    (352256*u+23690) (348160*u+23414) (by omega) hS1
  have hfan := BB6.Agent3ParentFan.even_even_parent_fan a k
    (352256*u+23690) (348160*u+23414)
    (by omega) (by omega) (by omega) (by omega) hstep
  rcases hfan with hdirect | hzero | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    obtain ⟨haEq,hkEq⟩ := s1_direct_parent_coordinates u a k ha hk
    left
    simpa only [haEq,hkEq] using hprev
  · rcases hzero with ⟨ha0,hk2,n,hxy,_⟩
    have hsumPow : 2^11*(342*u+23)=2^(n+3) := by
      calc
        2^11*(342*u+23) =
            (352256*u+23690)+(348160*u+23414) := (s1_sum_valuation u).symm
        _ = 2^n*8 := hxy
        _ = 2^n*2^3 := by rw [show 8=2^3 by decide]
        _ = 2^(n+3) := by rw [← Nat.pow_add]
    rcases s1_odd_quotient_facts u with ⟨hodd,hgt⟩
    exact False.elim (no_pow_two_times_odd_gt_one (342*u+23) n hodd hgt hsumPow)
  · rcases hbounce with ⟨ha2,haeven,hkpos,halt,n,hnodd,hxy,hcost⟩
    have hnle := s1_bounce_depth_le_nine u a n hnodd hxy
    have hcases := s1_bounce_parent_cases u a k n hnodd hnle hxy hcost
    rcases hcases with hP1 | hP3 | hB0 | hP7 | hP9
    · rcases hP1 with ⟨haEq,hkEq⟩
      have hfacts := s1_p1_parent_facts u a k haEq hkEq
      exact False.elim (run_no_odd_sum_one a k hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2 hprev)
    · rcases hP3 with ⟨haEq,hkEq⟩
      have hP3 : RunReach (43776*u+2942) (502400*u+33780) := by
        simpa only [haEq,hkEq] using hprev
      have hfacts := s1_p3_evenright_facts u
      have hP3D := run_evenright_parent
        (43776*u+2942) (502400*u+33780)
        hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2 hP3
      have hcoords := s1_p3_evenright_coordinates u
      have hP3D' : RunReach (546176*u+36720) (251200*u+16889) := by
        simpa only [hcoords.1,hcoords.2] using hP3D
      have hfacts' := s1_p3d_odd_sum_one_facts u
      exact False.elim (run_no_odd_sum_one
        (546176*u+36720) (251200*u+16889) hfacts'.1 hfacts'.2.1 hfacts'.2.2.1 hfacts'.2.2.2 hP3D')
    · rcases hB0 with ⟨haEq,hkEq⟩
      exact False.elim (hB0 (by simpa only [haEq,hkEq] using hprev))
    · rcases hP7 with ⟨haEq,hkEq⟩
      right
      simpa only [haEq,hkEq] using hprev
    · rcases hP9 with ⟨haEq,hkEq⟩
      have hP9 : RunReach (684*u+44) (523946*u+35220) := by
        simpa only [haEq,hkEq] using hprev
      have hfacts := s1_p9_evenright_facts u hu8
      have hP9D := run_evenright_parent
        (684*u+44) (523946*u+35220)
        hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2 hP9
      have hu4 : u%4=2 := by omega
      have hcoords := s1_p9_evenright_coordinates u
      have hP9D' : RunReach (524630*u+35262) (261973*u+17609) := by
        simpa only [hcoords.1,hcoords.2] using hP9D
      have hfacts' := s1_p9d_odd_sum_one_facts u hu4
      exact False.elim (run_no_odd_sum_one
        (524630*u+35262) (261973*u+17609) hfacts'.1 hfacts'.2.1 hfacts'.2.2.1 hfacts'.2.2.2 hP9D')


/-- Root-parameter wrapper supplying the exact B0 exclusion. -/
theorem S1_reach_implies_D0_or_P7_of_root (r E u : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13))
    (hu8 : u%8=2)
    (hS1 : RunReach (352256*u+23690) (348160*u+23414)) :
    RunReach (700416*u+47102) (174080*u+11706) ∨
    RunReach (2736*u+182) (522920*u+35154) := by
  have hB0 := root32_b0_unreachable r E u hr64 hE hRoot
  exact S1_reach_implies_D0_or_P7 u hu8 hB0 hS1

end BB6.Agent3Root32HighStopS1

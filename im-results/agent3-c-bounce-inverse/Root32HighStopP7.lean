import Root32HighStopIntegrated
import Root32HighStopS1
import EvenEvenParentFan
import EvenRightUnique
import M0EvenEvenSumZero
import U5B2Root32
import U5B2Root32ParameterBridge
import Agent3CImage
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3Root32HighStopP7
open BB6.Agent46
open BB6.Agent3Root32HighStopIntegrated
open BB6.Agent3Root32HighStopS1

/-- The root32 progression fixes both low residue classes of u. -/
theorem root32_u_moduli (t : Nat) :
    (1802+6720*t)%8=2 ∧ (1802+6720*t)%16=10 := by
  constructor <;> omega

/-- Exact coordinate conversions along the P7 direct-parent route. -/
theorem p7_direct_coordinates (u : Nat) :
    (2736*u+182)+(522920*u+35154)=525656*u+35336 ∧
    (2736*u+182)+(522920*u+35154)-2=525656*u+35334 ∧
    (522920*u+35154-2)/2=261460*u+17576 ∧
    (525656*u+35334)+(261460*u+17576)-2=787116*u+52908 ∧
    (261460*u+17576-2)/2=130730*u+8787 := by
  constructor <;> omega

/-- Exact P7 direct-branch even-right conditions. -/
theorem p7_direct_evenright_facts (u : Nat) (hu8 : u%8=2) :
    5<525656*u+35334 ∧ 6≤261460*u+17576 ∧
    (261460*u+17576)%2=0 ∧
    ((525656*u+35334)+(261460*u+17576))%8≠0 ∧
    ((525656*u+35334)+(261460*u+17576))%8≠7 := by
  constructor <;> omega

/-- Exact P7 direct second-parent coordinates. -/
theorem p7_direct_second_parent_coordinates (u : Nat) :
    (787116*u+52908)+(130730*u+8787)+1=917846*u+61696 ∧
    (787116*u+52908)+2*(130730*u+8787)=1048576*u+70482 := by
  constructor <;> omega

/-- The even/odd parent of the P7 direct second parent is R2. -/
theorem p7_direct_r2_coordinates (u : Nat) (a k : Nat)
    (ha : a=(787116*u+52908+130730*u+8787+1)/2-3)
    (hk : k=(787116*u+52908+2*(130730*u+8787)-a-7)/2) :
    a=458923*u+30845 ∧ k=(589653*u+39630)/2 := by
  constructor <;> omega

/-- R2 is an even-right target precisely on the root32 u residue. -/
theorem p7_direct_r2_evenright_facts (u : Nat) (hu16 : u%16=10) :
    5<458923*u+30845 ∧ 6≤(589653*u+39630)/2 ∧
    ((589653*u+39630)/2)%2=0 ∧
    ((458923*u+30845)+((589653*u+39630)/2))%8≠0 ∧
    ((458923*u+30845)+((589653*u+39630)/2))%8≠7 := by
  constructor <;> omega

/-- Convert the final R2 even-right parent to the named L(t) target. -/
theorem p7_direct_L_coordinates (t u : Nat) (hu : u=1802+6720*t) :
    (458923*u+30845)+((589653*u+39630)/2)-2=
      5065196640*t+1358307257 ∧
    (((589653*u+39630)/2)-2)/2=990617040*t+265648583 := by
  rw [hu]
  constructor <;> omega

/-- Exact coordinate conversions on the corrected P7 bounce branch. -/
theorem p7_bounce_coordinates (u : Nat) :
    2*(65707*u+4417)-2=131414*u+8832 ∧
    ((2736*u+182)+2*(522920*u+35154)-2*(65707*u+4417)-8)/2=
      458581*u+30824 ∧
    (131414*u+8832)+(458581*u+30824)-2=589995*u+39654 ∧
    (458581*u+30824-2)/2=(458581*u+30822)/2 := by
  constructor <;> omega

/-- The corrected P7 bounce target has a valid even-right parent. -/
theorem p7_bounce_evenright_facts (u : Nat) (hu8 : u%8=2) :
    5<131414*u+8832 ∧ 6≤458581*u+30824 ∧
    (458581*u+30824)%2=0 ∧
    ((131414*u+8832)+(458581*u+30824))%8≠0 ∧
    ((131414*u+8832)+(458581*u+30824))%8≠7 := by
  constructor <;> omega

/-- The corrected first parent of P7E has exact t-coordinates. -/
theorem p7e1_coordinates (t u : Nat) (hu : u=1802+6720*t) :
    589995*u+39654=3964766400*t+1063210644 ∧
    (458581*u+30822)/2=1540832160*t+413196892 := by
  rw [hu]
  constructor <;> omega

/-- The corrected P7E1 sum-zero quotient and its two parent formulas. -/
theorem p7e1_sumzero_facts (t : Nat) :
    (3964766400*t+1063210644)+(1540832160*t+413196892)=
      8*(688199820*t+184550942) ∧
    (688199820*t+184550942)%4=2 ∧ 2<688199820*t+184550942 := by
  constructor <;> omega

theorem p7e1_parent_coordinates (t a k : Nat)
    (ha : a=(3964766400*t+1063210644)+(1540832160*t+413196892)-2)
    (hk : k=(1540832160*t+413196892-2)/2) :
    a=5505598560*t+1476407534 ∧ k=770416080*t+206598445 := by
  constructor <;> omega

theorem p7e1_bounce_parent_coordinates (t a k : Nat)
    (ha : a=2*(688199820*t+184550942)-2)
    (hk : k=((3964766400*t+1063210644)+2*(1540832160*t+413196892)-
      2*(688199820*t+184550942)-8)/2) :
    a=1376399640*t+369101882 ∧ k=2835015540*t+760251268 := by
  constructor <;> omega

/-- The direct P7E1 parent is even/odd with the v2-two parent gate. -/
theorem p7e2_parent_gate_facts (t : Nat) :
    (5505598560*t+1476407534)%2=0 ∧
    (770416080*t+206598445)%2=1 ∧
    8<770416080*t+206598445 ∧
    ((5505598560*t+1476407534)+(770416080*t+206598445))%2=1 ∧
    ((5505598560*t+1476407534)+(770416080*t+206598445)+1)%8=4 := by
  constructor <;> omega

/-- The resulting odd/odd parent has sum two modulo four and is
therefore excluded by the source-certified odd-image invariant. -/
theorem p7e2_parent_no_image_facts (t : Nat) :
    5<3138007320*t+841502987 ∧
    5≤1954211700*t+524050715 ∧
    (1954211700*t+524050715)%2=1 ∧
    ((3138007320*t+841502987)+(1954211700*t+524050715))%4=2 := by
  constructor <;> omega

/-- A blank return to P7 forces either the old L(t) branch or the
corrected new residual P7E1E(t). The latter is not claimed unreachable. -/
theorem P7_reach_implies_L_or_P7E1E (t : Nat)
    (hP7 : RunReach (2736*(1802+6720*t)+182)
      (522920*(1802+6720*t)+35154)) :
    RunReach (5065196640*t+1358307257) (990617040*t+265648583) ∨
    RunReach (1376399640*t+369101882) (2835015540*t+760251268) := by
  let u := 1802+6720*t
  have hu8 : u%8=2 := by simpa [u] using (root32_u_moduli t).1
  have hu16 : u%16=10 := by simpa [u] using (root32_u_moduli t).2
  obtain ⟨a,k,hprev,hstep⟩ := run_parent_of_left_gt5
    (2736*u+182) (522920*u+35154) (by omega) (by simpa [u] using hP7)
  have hsumP7 : (2736*u+182)+(522920*u+35154)=8*(65707*u+4417) := by omega
  have hfan := BB6.Agent11M0SumZeroVerified.even_even_sumzero_parent
    a k (2736*u+182) (522920*u+35154) (65707*u+4417)
    (by omega) (by omega) (by omega) (by omega) hsumP7 (by omega) (by omega) hstep
  rcases hfan with hdirect | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    have hcoords := p7_direct_coordinates u
    have haEq : a=525656*u+35334 := by omega
    have hkEq : k=261460*u+17576 := by omega
    have hP7D : RunReach (525656*u+35334) (261460*u+17576) := by
      simpa only [haEq,hkEq] using hprev
    have hfacts := p7_direct_evenright_facts u hu8
    have hR1 := run_evenright_parent
      (525656*u+35334) (261460*u+17576)
      hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2 hP7D
    have hR1x := hcoords.2.2.2.1
    have hR1y := hcoords.2.2.2.2
    have hR1' : RunReach (787116*u+52908) (130730*u+8787) := by
      simpa only [hR1x,hR1y] using hR1
    obtain ⟨a1,k1,hprev1,hstep1⟩ := run_parent_of_left_gt5
      (787116*u+52908) (130730*u+8787) (by omega) hR1'
    have hx1 : (787116*u+52908)%2=0 := by omega
    have hy1 : (130730*u+8787)%2=1 := by omega
    have hy81 : 8<130730*u+8787 := by omega
    have hsum1 : ((787116*u+52908)+(130730*u+8787))%2=1 := by omega
    have hval1 : ((787116*u+52908)+(130730*u+8787)+1)%8=4 := by
      have hEq : (787116*u+52908)+(130730*u+8787)+1=917846*u+61696 := by omega
      rw [hEq]
      omega
    obtain ⟨ha1,hk1⟩ := evenodd_sumplusone_v2two_parent
      (787116*u+52908) (130730*u+8787) a1 k1 hx1 hy1 hy81 hsum1 hval1 hstep1
    have ha1Eq : a1=458923*u+30845 := by omega
    have hk1Eq : k1=(589653*u+39630)/2 := by omega
    have hR2 : RunReach (458923*u+30845) ((589653*u+39630)/2) := by
      simpa only [ha1Eq,hk1Eq] using hprev1
    have hfacts2 := p7_direct_r2_evenright_facts u hu16
    have hL := run_evenright_parent
      (458923*u+30845) ((589653*u+39630)/2)
      hfacts2.1 hfacts2.2.1 hfacts2.2.2.1 hfacts2.2.2.2.1 hfacts2.2.2.2.2 hR2
    have hLcoords := p7_direct_L_coordinates t u (by rfl)
    have hL' : RunReach (5065196640*t+1358307257) (990617040*t+265648583) := by
      simpa only [hLcoords.1,hLcoords.2] using hL
    exact Or.inl hL'
  · rcases hbounce with ⟨ha,hk⟩
    have hcoords := p7_bounce_coordinates u
    have haEq : a=131414*u+8832 := by omega
    have hkEq : k=458581*u+30824 := by omega
    have hP7E : RunReach (131414*u+8832) (458581*u+30824) := by
      simpa only [haEq,hkEq] using hprev
    have hfacts := p7_bounce_evenright_facts u hu8
    have hP7E1 := run_evenright_parent
      (131414*u+8832) (458581*u+30824)
      hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2 hP7E
    have hcoordsE1 := p7e1_coordinates t u (by rfl)
    have hP7E1' : RunReach (3964766400*t+1063210644) (1540832160*t+413196892) := by
      simpa only [hcoords.2.2.1,hcoords.2.2.2,hcoordsE1.1,hcoordsE1.2] using hP7E1
    obtain ⟨a1,k1,hprev1,hstep1⟩ := run_parent_of_left_gt5
      (3964766400*t+1063210644) (1540832160*t+413196892) (by omega) hP7E1'
    have hsumE1 := p7e1_sumzero_facts t
    have hfanE1 := BB6.Agent11M0SumZeroVerified.even_even_sumzero_parent
      a1 k1 (3964766400*t+1063210644) (1540832160*t+413196892)
      (688199820*t+184550942)
      (by omega) (by omega) (by omega) (by omega)
      hsumE1.1 (by omega) (by omega) hstep1
    rcases hfanE1 with hdirectE1 | hbounceE1
    · rcases hdirectE1 with ⟨haE1,hkE1⟩
      have hcoordsE2 := p7e1_parent_coordinates t a1 k1 haE1 hkE1
      have hP7E2 : RunReach (5505598560*t+1476407534) (770416080*t+206598445) := by
        simpa only [hcoordsE2.1,hcoordsE2.2] using hprev1
      obtain ⟨a2,k2,hprev2,hstep2⟩ := run_parent_of_left_gt5
        (5505598560*t+1476407534) (770416080*t+206598445) (by omega) hP7E2
      have hfactsE2 := p7e2_parent_gate_facts t
      obtain ⟨ha2,hk2⟩ := evenodd_sumplusone_v2two_parent
        (5505598560*t+1476407534) (770416080*t+206598445) a2 k2
        hfactsE2.1 hfactsE2.2.1 hfactsE2.2.2.1 hfactsE2.2.2.2.1 hfactsE2.2.2.2.2 hstep2
      have ha2Eq : a2=3138007320*t+841502987 := by omega
      have hk2Eq : k2=1954211700*t+524050715 := by omega
      have hA2 : RunReach (3138007320*t+841502987) (1954211700*t+524050715) := by
        simpa only [ha2Eq,hk2Eq] using hprev2
      have hno := p7e2_parent_no_image_facts t
      exact False.elim (run_no_odd_sum_two
        (3138007320*t+841502987) (1954211700*t+524050715)
        hno.1 hno.2.1 hno.2.2.1 hno.2.2.2 hA2)
    · rcases hbounceE1 with ⟨haE1,hkE1⟩
      have hcoordsE1E := p7e1_bounce_parent_coordinates t a1 k1 haE1 hkE1
      have hP7E1E : RunReach (1376399640*t+369101882) (2835015540*t+760251268) := by
        simpa only [hcoordsE1E.1,hcoordsE1E.2] using hprev1
      exact Or.inr hP7E1E

/-- Exact D0 parent coordinates and the even-right direct-parent gate. -/
theorem d0_parent_coordinates (u : Nat) :
    (700416*u+47102)+(174080*u+11706)-2=874496*u+58806 ∧
    (174080*u+11706-2)/2=87040*u+5852 ∧
    (874496*u+58806)+(87040*u+5852)-2=961536*u+64656 ∧
    (87040*u+5852-2)/2=43520*u+2925 := by
  constructor <;> omega

theorem d0_direct_evenright_facts (u : Nat) (hu8 : u%8=2) :
    5<874496*u+58806 ∧ 6≤87040*u+5852 ∧
    (87040*u+5852)%2=0 ∧
    ((874496*u+58806)+(87040*u+5852))%8≠0 ∧
    ((874496*u+58806)+(87040*u+5852))%8≠7 := by
  constructor <;> omega

theorem d0_direct_parent_odd_sum_one_facts (u : Nat) :
    5<961536*u+64656 ∧ 5≤43520*u+2925 ∧
    (43520*u+2925)%2=1 ∧
    ((961536*u+64656)+(43520*u+2925))%4=1 := by
  constructor <;> omega

theorem d0_bounce_coordinates (t u : Nat) (hu : u=1802+6720*t) :
    2*(109312*u+7351)-2=218624*u+14700 ∧
    ((700416*u+47102)+2*(174080*u+11706)-
      2*(109312*u+7351)-8)/2=414976*u+27902 ∧
    218624*u+14700=1469153280*t+393975148 ∧
    414976*u+27902=2788638720*t+747814654 := by
  rw [hu]
  constructor <;> omega

/-- D0 has only the D0E bounce parent: its direct parent has a unique
even-right parent with forbidden odd-right sum one. -/
theorem D0_reach_implies_D0E (t : Nat)
    (hD0 : RunReach (700416*(1802+6720*t)+47102)
      (174080*(1802+6720*t)+11706)) :
    RunReach (1469153280*t+393975148) (2788638720*t+747814654) := by
  let u := 1802+6720*t
  have hu8 : u%8=2 := by simpa [u] using (root32_u_moduli t).1
  obtain ⟨a,k,hprev,hstep⟩ := run_parent_of_left_gt5
    (700416*u+47102) (174080*u+11706) (by omega) (by simpa [u] using hD0)
  have hsumD0 : (700416*u+47102)+(174080*u+11706)=8*(109312*u+7351) := by omega
  have hfan := BB6.Agent11M0SumZeroVerified.even_even_sumzero_parent
    a k (700416*u+47102) (174080*u+11706) (109312*u+7351)
    (by omega) (by omega) (by omega) (by omega) hsumD0 (by omega) (by omega) hstep
  rcases hfan with hdirect | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    have hcoords := d0_parent_coordinates u
    have haEq : a=874496*u+58806 := by omega
    have hkEq : k=87040*u+5852 := by omega
    have hD0D : RunReach (874496*u+58806) (87040*u+5852) := by
      simpa only [haEq,hkEq] using hprev
    have hfacts := d0_direct_evenright_facts u hu8
    have hD0D1 := run_evenright_parent
      (874496*u+58806) (87040*u+5852)
      hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2 hD0D
    have hD0D1coords :
        (874496*u+58806)+(87040*u+5852)-2=961536*u+64656 ∧
        (87040*u+5852-2)/2=43520*u+2925 := ⟨hcoords.2.2.1,hcoords.2.2.2⟩
    have hD0D1' : RunReach (961536*u+64656) (43520*u+2925) := by
      simpa only [hD0D1coords.1,hD0D1coords.2] using hD0D1
    have hno := d0_direct_parent_odd_sum_one_facts u
    exact False.elim (run_no_odd_sum_one
      (961536*u+64656) (43520*u+2925)
      hno.1 hno.2.1 hno.2.2.1 hno.2.2.2 hD0D1')
  · rcases hbounce with ⟨ha,hk⟩
    have hcoords := d0_bounce_coordinates t u (by rfl)
    have haEq : a=218624*u+14700 := by omega
    have hkEq : k=414976*u+27902 := by omega
    have hD0E : RunReach (218624*u+14700) (414976*u+27902) := by
      simpa only [haEq,hkEq] using hprev
    have hD0E' : RunReach (1469153280*t+393975148) (2788638720*t+747814654) := by
      simpa only [hcoords.2.2.1,hcoords.2.2.2] using hD0E
    exact hD0E'

/-- Fully integrated root32 high-stop reduction. It uses the exact
root parameter bridge and the corrected S1/P7 source fans. The only
remaining alternatives are D0E(t), L(t), and the newly identified
P7E1E(t) residual. -/
theorem root32_highstop_reduces_to_three_residuals (r E u : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13))
    (hT : RunReach (1048576*u+70538) 3) :
    ∃ t, u=1802+6720*t ∧
      (RunReach (1469153280*t+393975148) (2788638720*t+747814654) ∨
       RunReach (5065196640*t+1358307257) (990617040*t+265648583) ∨
       RunReach (1376399640*t+369101882) (2835015540*t+760251268)) := by
  obtain ⟨t,hu⟩ := BB6.Agent3U5B2Root32ParameterBridge.root32_u_parameter_of_exact
    r E u hr64 hE hRoot
  have hu7 : u%7=3 := by rw [hu]; omega
  have huEven : u%2=0 := by rw [hu]; omega
  have hu8 : u%8=2 := by rw [hu]; omega
  have hQ := T_reach_implies_Q_reach u hu7 hT
  have hS3 := Q_reach_implies_S3_reach u huEven hQ
  have hS2 := S3_reach_implies_S2_reach u hS3
  have hS1 := S2_reach_implies_S1_reach u huEven hS2
  have hB0 := root32_b0_unreachable r E u hr64 hE hRoot
  have hfan := S1_reach_implies_D0_or_P7 u hu8 hB0 hS1
  rcases hfan with hD0 | hP7
  · refine ⟨t,hu,Or.inl ?_⟩
    exact D0_reach_implies_D0E t (by simpa [hu] using hD0)
  · have hP7' : RunReach (2736*(1802+6720*t)+182)
        (522920*(1802+6720*t)+35154) := by simpa [hu] using hP7
    have hres := P7_reach_implies_L_or_P7E1E t hP7'
    rcases hres with hL | hP7E1E
    · exact ⟨t,hu,Or.inr (Or.inl hL)⟩
    · exact ⟨t,hu,Or.inr (Or.inr hP7E1E)⟩

end BB6.Agent3Root32HighStopP7

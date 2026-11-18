import U5Q0SecondaryFan
import EvenRightUnique
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

/-!
Exact source-parent closure for the U5 q=0 secondary fan on
h = 16 (mod 32).  The even/even quotient has 2-adic valuation exactly
five, so only bounce depths r=1,2 occur.  Every direct/bounce alternative
normalizes by exact original-section inverses to the forbidden
odd-right, sum-one-mod-four blank image.

This is an intermediate source proof draft pending exact local preflight
and CI; it is not a BB(6) solution.
-/

namespace BB6.Agent3U5Q0H16

private theorem even_right_parent_of_reach
    (x y : Nat)
    (hy6 : 6 ≤ y) (hye : y % 2 = 0)
    (hzero : (x+y) % 8 ≠ 0) (hseven : (x+y) % 8 ≠ 7)
    (h : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
  have hrun :
      (∃ t : Nat, BB6.Agent8Section.run BB6.Agent46.secNext t
        (some (5,1)) = some (x,y)) := by
    simpa [BB6.Agent3.CReach] using h
  have hparent :=
    (BB6.Agent15.blank_reach_iff_even_right
      x y hy6 hye hzero hseven).mp hrun
  simpa [BB6.Agent3.CReach] using hparent

/-- The direct parent E_h is excluded by four exact even-right inverse
steps, ending at an odd-right state with sum 1 modulo four. -/
theorem u5_q0_h16_E_unreachable (u : Nat) :
    ¬ BB6.Agent3.CReach (28364+54656*u) (53838+103744*u) := by
  intro h0
  have h1 : BB6.Agent3.CReach
      (82200+158400*u) (26918+51872*u) := by
    have hp := even_right_parent_of_reach
      (28364+54656*u) (53838+103744*u)
      (by omega) (by omega) (by omega) (by omega) h0
    have hx :
        (28364+54656*u)+(53838+103744*u)-2 =
          82200+158400*u := by omega
    have hy :
        ((53838+103744*u)-2)/2 = 26918+51872*u := by omega
    simpa only [hx,hy] using hp
  have h2 : BB6.Agent3.CReach
      (109116+210272*u) (13458+25936*u) := by
    have hp := even_right_parent_of_reach
      (82200+158400*u) (26918+51872*u)
      (by omega) (by omega) (by omega) (by omega) h1
    have hx :
        (82200+158400*u)+(26918+51872*u)-2 =
          109116+210272*u := by omega
    have hy :
        ((26918+51872*u)-2)/2 = 13458+25936*u := by omega
    simpa only [hx,hy] using hp
  have h3 : BB6.Agent3.CReach
      (122572+236208*u) (6728+12968*u) := by
    have hp := even_right_parent_of_reach
      (109116+210272*u) (13458+25936*u)
      (by omega) (by omega) (by omega) (by omega) h2
    have hx :
        (109116+210272*u)+(13458+25936*u)-2 =
          122572+236208*u := by omega
    have hy :
        ((13458+25936*u)-2)/2 = 6728+12968*u := by omega
    simpa only [hx,hy] using hp
  have h4 : BB6.Agent3.CReach
      (129298+249176*u) (3363+6484*u) := by
    have hp := even_right_parent_of_reach
      (122572+236208*u) (6728+12968*u)
      (by omega) (by omega) (by omega) (by omega) h3
    have hx :
        (122572+236208*u)+(6728+12968*u)-2 =
          129298+249176*u := by omega
    have hy :
        ((6728+12968*u)-2)/2 = 3363+6484*u := by omega
    simpa only [hx,hy] using hp
  exact
    (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (129298+249176*u) (3363+6484*u)
      (by omega) (by omega) (by omega) (by omega) h4)

/-- The depth-one bounce parent B_(1,h) is excluded by one exact
even-right inverse step, ending at the forbidden odd-right image. -/
theorem u5_q0_h16_B1_unreachable (u : Nat) :
    ¬ BB6.Agent3.CReach (5678+10944*u) (65180+125600*u) := by
  intro h0
  have h1 : BB6.Agent3.CReach
      (70856+136544*u) (32589+62800*u) := by
    have hp := even_right_parent_of_reach
      (5678+10944*u) (65180+125600*u)
      (by omega) (by omega) (by omega) (by omega) h0
    have hx :
        (5678+10944*u)+(65180+125600*u)-2 =
          70856+136544*u := by omega
    have hy :
        ((65180+125600*u)-2)/2 = 32589+62800*u := by omega
    simpa only [hx,hy] using hp
  exact
    (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (70856+136544*u) (32589+62800*u)
      (by omega) (by omega) (by omega) (by omega) h1)

/-- The depth-two bounce parent B_(2,h) is itself in the forbidden
odd-right, sum-one-mod-four blank image. -/
theorem u5_q0_h16_B2_unreachable (u : Nat) :
    ¬ BB6.Agent3.CReach (1418+2736*u) (67307+129704*u) := by
  exact
    BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (1418+2736*u) (67307+129704*u)
      (by omega) (by omega) (by omega) (by omega)

/-- New infinite q=0 secondary-parent cylinder: P0 is blank-unreachable
for every h=16+32*u.  The exact parent fan leaves E_h or B_(r,h);
the quotient valuation forces r=1 or 2, and all three possibilities
are excluded above. -/
theorem u5_q0_secondary_parent_unreachable_h16 (u : Nat) :
    ¬ BB6.Agent3.CReach
      (1674+2752*(16+32*u)) (1654+2720*(16+32*u)) := by
  intro hP
  have hred :=
    BB6.Agent11U5Q0SecondaryFan.u5_q0_secondary_parent_reduction
      (16+32*u) hP
  rcases hred with hE | ⟨r,q,hr,hpow,hB⟩
  · have hx :
        1036+1708*(16+32*u)=28364+54656*u := by omega
    have hy :
        1966+3242*(16+32*u)=53838+103744*u := by omega
    have hE' : BB6.Agent3.CReach
        (28364+54656*u) (53838+103744*u) := by
      simpa only [hx,hy] using hE
    exact u5_q0_h16_E_unreachable u hE'
  · have hSfactor :
        416+684*(16+32*u)=32*(355+684*u) := by omega
    have hWodd : ∃ v, 355+684*u=2*v+1 := by
      exact ⟨342*u+177, by omega⟩
    rcases hWodd with ⟨v,hv⟩
    have hSmod64 :
        (416+684*(16+32*u))%64=32 := by
      rw [hSfactor,hv]
      omega
    have hrle : r≤2 := by
      by_contra hnot
      have hr3 : 3≤r := by omega
      have h64pow : 64∣4^r := by
        have hpowdiv : (4:Nat)^3∣4^r :=
          Nat.pow_dvd_pow 4 hr3
        simpa only [show (4:Nat)^3=64 by norm_num] using hpowdiv
      have h64S : 64∣416+684*(16+32*u) := by
        rcases h64pow with ⟨d,hd⟩
        refine ⟨d*q,?_⟩
        calc
          416+684*(16+32*u) = 4^r*q := hpow.symm
          _ = (64*d)*q := by rw [hd]
          _ = 64*(d*q) := by ring
      have hSzero := Nat.dvd_iff_mod_eq_zero.mp h64S
      omega
    have hrcases : r=1 ∨ r=2 := by omega
    rcases hrcases with hr1 | hr2
    · have hpow1 := hpow
      rw [hr1] at hpow1
      norm_num at hpow1
      have hq : q=2840+5472*u := by omega
      have hx : 2*q-2=5678+10944*u := by rw [hq]; omega
      have hy :
          2487+4096*(16+32*u)-q-3*r=65180+125600*u := by
        rw [hr1,hq]
        omega
      have hB1 : BB6.Agent3.CReach
          (5678+10944*u) (65180+125600*u) := by
        simpa only [hx,hy] using hB
      exact u5_q0_h16_B1_unreachable u hB1
    · have hpow2 := hpow
      rw [hr2] at hpow2
      norm_num at hpow2
      have hq : q=710+1368*u := by omega
      have hx : 2*q-2=1418+2736*u := by rw [hq]; omega
      have hy :
          2487+4096*(16+32*u)-q-3*r=67307+129704*u := by
        rw [hr2,hq]
        omega
      have hB2 : BB6.Agent3.CReach
          (1418+2736*u) (67307+129704*u) := by
        simpa only [hx,hy] using hB
      exact u5_q0_h16_B2_unreachable u hB2

#print axioms u5_q0_h16_E_unreachable
#print axioms u5_q0_h16_B1_unreachable
#print axioms u5_q0_h16_B2_unreachable
#print axioms u5_q0_secondary_parent_unreachable_h16

end BB6.Agent3U5Q0H16

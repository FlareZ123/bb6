import U5Q0SecondaryFan
import EvenRightUnique
import M0EvenEvenSumZero
import OddSevenOrbit
import ReachAffine
import HighSumTwo
import Lean.Elab.Tactic.Omega

/-!
Exact source-parent closure for the U5 q=0 secondary fan on
h = 40 (mod 128).  The quotient has 2-adic valuation exactly seven,
so only bounce depths r=1,2,3 occur.  All direct/bounce alternatives
reduce by exact original-section inverses to the forbidden odd-right
sum-one or sum-two blank-image cylinders.

Intermediate proof draft pending exact local preflight and CI.
-/

namespace BB6.Agent3U5Q0H40

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

private theorem even_seven_parent_of_reach
    (x y : Nat)
    (hx : x % 2 = 0) (hy : y % 2 = 1) (hy5 : 5 ≤ y)
    (hs : (x+y+1) % 16 = 8) (hsize : 23 ≤ x+y)
    (h : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach ((x+y-5)/2) ((x+3*y-9)/4) := by
  have hrun :
      (∃ t : Nat, BB6.Agent8Section.run BB6.Agent46.secNext t
        (some (5,1)) = some (x,y)) := by
    simpa [BB6.Agent3.CReach] using h
  have hparent :=
    (BB6.Agent3.odd_seven_blank_reach_iff
      x y hx hy hy5 hs hsize).mp hrun
  simpa [BB6.Agent3.CReach] using hparent

private theorem even_affine_parent_of_reach
    (x y : Nat)
    (hy4 : 4 ≤ y) (hye : y % 2 = 0) (hs : (x+y) % 4 = 1)
    (h : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
  have hrun :
      (∃ t : Nat, BB6.Agent8Section.run BB6.Agent46.secNext t
        (some (5,1)) = some (x,y)) := by
    simpa [BB6.Agent3.CReach] using h
  have hparent :=
    (BB6.Agent15.blank_reach_iff_affine
      x y hy4 hye hs).mp hrun
  simpa [BB6.Agent3.CReach] using hparent

/-- E_h takes six exact even-right inverse steps to an odd-right
sum-one-mod-four state. -/
theorem u5_q0_h40_E_unreachable (u : Nat) :
    ¬ BB6.Agent3.CReach (69356+218624*u) (131646+414976*u) := by
  intro h0
  have h1 : BB6.Agent3.CReach
      (201000+633600*u) (65822+207488*u) := by
    have hp := even_right_parent_of_reach
      (69356+218624*u) (131646+414976*u)
      (by omega) (by omega) (by omega) (by omega) h0
    have hx :
        (69356+218624*u)+(131646+414976*u)-2 =
          201000+633600*u := by omega
    have hy :
        ((131646+414976*u)-2)/2 = 65822+207488*u := by omega
    simpa only [hx,hy] using hp
  have h2 : BB6.Agent3.CReach
      (266820+841088*u) (32910+103744*u) := by
    have hp := even_right_parent_of_reach
      (201000+633600*u) (65822+207488*u)
      (by omega) (by omega) (by omega) (by omega) h1
    have hx :
        (201000+633600*u)+(65822+207488*u)-2 =
          266820+841088*u := by omega
    have hy :
        ((65822+207488*u)-2)/2 = 32910+103744*u := by omega
    simpa only [hx,hy] using hp
  have h3 : BB6.Agent3.CReach
      (299728+944832*u) (16454+51872*u) := by
    have hp := even_right_parent_of_reach
      (266820+841088*u) (32910+103744*u)
      (by omega) (by omega) (by omega) (by omega) h2
    have hx :
        (266820+841088*u)+(32910+103744*u)-2 =
          299728+944832*u := by omega
    have hy :
        ((32910+103744*u)-2)/2 = 16454+51872*u := by omega
    simpa only [hx,hy] using hp
  have h4 : BB6.Agent3.CReach
      (316180+996704*u) (8226+25936*u) := by
    have hp := even_right_parent_of_reach
      (299728+944832*u) (16454+51872*u)
      (by omega) (by omega) (by omega) (by omega) h3
    have hx :
        (299728+944832*u)+(16454+51872*u)-2 =
          316180+996704*u := by omega
    have hy :
        ((16454+51872*u)-2)/2 = 8226+25936*u := by omega
    simpa only [hx,hy] using hp
  have h5 : BB6.Agent3.CReach
      (324404+1022640*u) (4112+12968*u) := by
    have hp := even_right_parent_of_reach
      (316180+996704*u) (8226+25936*u)
      (by omega) (by omega) (by omega) (by omega) h4
    have hx :
        (316180+996704*u)+(8226+25936*u)-2 =
          324404+1022640*u := by omega
    have hy :
        ((8226+25936*u)-2)/2 = 4112+12968*u := by omega
    simpa only [hx,hy] using hp
  have h6 : BB6.Agent3.CReach
      (328514+1035608*u) (2055+6484*u) := by
    have hp := even_right_parent_of_reach
      (324404+1022640*u) (4112+12968*u)
      (by omega) (by omega) (by omega) (by omega) h5
    have hx :
        (324404+1022640*u)+(4112+12968*u)-2 =
          328514+1035608*u := by omega
    have hy :
        ((4112+12968*u)-2)/2 = 2055+6484*u := by omega
    simpa only [hx,hy] using hp
  exact
    (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (328514+1035608*u) (2055+6484*u)
      (by omega) (by omega) (by omega) (by omega) h6)

/-- B_(1,h) takes one exact even-right inverse step to the
forbidden odd-right sum-one-mod-four image. -/
theorem u5_q0_h40_B1_unreachable (u : Nat) :
    ¬ BB6.Agent3.CReach (13886+43776*u) (159380+502400*u) := by
  intro h0
  have h1 : BB6.Agent3.CReach
      (173264+546176*u) (79689+251200*u) := by
    have hp := even_right_parent_of_reach
      (13886+43776*u) (159380+502400*u)
      (by omega) (by omega) (by omega) (by omega) h0
    have hx :
        (13886+43776*u)+(159380+502400*u)-2 =
          173264+546176*u := by omega
    have hy :
        ((159380+502400*u)-2)/2 = 79689+251200*u := by omega
    simpa only [hx,hy] using hp
  exact
    (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (173264+546176*u) (79689+251200*u)
      (by omega) (by omega) (by omega) (by omega) h1)

/-- B_(2,h) takes an exact even/odd seven-sector inverse and then
an affine even-right inverse, ending in the forbidden sum-two image. -/
theorem u5_q0_h40_B2_unreachable (u : Nat) :
    ¬ BB6.Agent3.CReach (3470+10944*u) (164585+518816*u) := by
  intro h0
  have h1 : BB6.Agent3.CReach
      (84025+264880*u) (124304+391848*u) := by
    have hp := even_seven_parent_of_reach
      (3470+10944*u) (164585+518816*u)
      (by omega) (by omega) (by omega) (by omega) (by omega) h0
    have hx :
        ((3470+10944*u)+(164585+518816*u)-5)/2 =
          84025+264880*u := by omega
    have hy :
        ((3470+10944*u)+3*(164585+518816*u)-9)/4 =
          124304+391848*u := by omega
    simpa only [hx,hy] using hp
  have h2 : BB6.Agent3.CReach
      (208327+656728*u) (62151+195924*u) := by
    have hp := even_affine_parent_of_reach
      (84025+264880*u) (124304+391848*u)
      (by omega) (by omega) (by omega) h1
    have hx :
        (84025+264880*u)+(124304+391848*u)-2 =
          208327+656728*u := by omega
    have hy :
        ((124304+391848*u)-2)/2 = 62151+195924*u := by omega
    simpa only [hx,hy] using hp
  exact
    (BB6.Agent11High.blank_no_odd_sum_two
      (208327+656728*u) (62151+195924*u)
      (by omega) (by omega) (by omega) h2)

/-- B_(3,h) takes one exact even-right inverse step to the
forbidden odd-right sum-one-mod-four image. -/
theorem u5_q0_h40_B3_unreachable (u : Nat) :
    ¬ BB6.Agent3.CReach (866+2736*u) (165884+522920*u) := by
  intro h0
  have h1 : BB6.Agent3.CReach
      (166748+525656*u) (82941+261460*u) := by
    have hp := even_right_parent_of_reach
      (866+2736*u) (165884+522920*u)
      (by omega) (by omega) (by omega) (by omega) h0
    have hx :
        (866+2736*u)+(165884+522920*u)-2 =
          166748+525656*u := by omega
    have hy :
        ((165884+522920*u)-2)/2 = 82941+261460*u := by omega
    simpa only [hx,hy] using hp
  exact
    (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (166748+525656*u) (82941+261460*u)
      (by omega) (by omega) (by omega) (by omega) h1)

/-- New infinite q=0 secondary-parent cylinder: P0 is blank-unreachable
for every h=40+128*u.  The exact parent fan leaves E_h or B_(r,h);
the quotient valuation forces r=1,2,3, and all four alternatives
are excluded above. -/
theorem u5_q0_secondary_parent_unreachable_h40 (u : Nat) :
    ¬ BB6.Agent3.CReach
      (1674+2752*(40+128*u)) (1654+2720*(40+128*u)) := by
  intro hP
  have hred :=
    BB6.Agent11U5Q0SecondaryFan.u5_q0_secondary_parent_reduction
      (40+128*u) hP
  rcases hred with hE | ⟨r,q,hr,hpow,hB⟩
  · have hx :
        1036+1708*(40+128*u)=69356+218624*u := by omega
    have hy :
        1966+3242*(40+128*u)=131646+414976*u := by omega
    have hE' : BB6.Agent3.CReach
        (69356+218624*u) (131646+414976*u) := by
      simpa only [hx,hy] using hE
    exact u5_q0_h40_E_unreachable u hE'
  · have hSfactor :
        416+684*(40+128*u)=128*(217+684*u) := by omega
    have hWodd : ∃ v, 217+684*u=2*v+1 := by
      exact ⟨342*u+108, by omega⟩
    rcases hWodd with ⟨v,hv⟩
    have hSmod256 :
        (416+684*(40+128*u))%256=128 := by
      rw [hSfactor,hv]
      omega
    have hrle : r≤3 := by
      by_contra hnot
      have hr4 : 4≤r := by omega
      have h256pow : 256∣4^r := by
        have hpowdiv : (4:Nat)^4∣4^r :=
          Nat.pow_dvd_pow 4 hr4
        simpa only [show (4:Nat)^4=256 by norm_num] using hpowdiv
      have h256S : 256∣416+684*(40+128*u) := by
        rcases h256pow with ⟨d,hd⟩
        refine ⟨d*q,?_⟩
        calc
          416+684*(40+128*u) = 4^r*q := hpow.symm
          _ = (256*d)*q := by rw [hd]
          _ = 256*(d*q) := by ring
      have hSzero := Nat.dvd_iff_mod_eq_zero.mp h256S
      omega
    have hrcases : r=1 ∨ r=2 ∨ r=3 := by omega
    rcases hrcases with hr1 | hr2 | hr3
    · have hpow1 := hpow
      rw [hr1] at hpow1
      norm_num at hpow1
      have hq : q=6944+21888*u := by omega
      have hx : 2*q-2=13886+43776*u := by rw [hq]; omega
      have hy :
          2487+4096*(40+128*u)-q-3*r=159380+502400*u := by
        rw [hr1,hq]
        omega
      have hB1 : BB6.Agent3.CReach
          (13886+43776*u) (159380+502400*u) := by
        simpa only [hx,hy] using hB
      exact u5_q0_h40_B1_unreachable u hB1
    · have hpow2 := hpow
      rw [hr2] at hpow2
      norm_num at hpow2
      have hq : q=1736+5472*u := by omega
      have hx : 2*q-2=3470+10944*u := by rw [hq]; omega
      have hy :
          2487+4096*(40+128*u)-q-3*r=164585+518816*u := by
        rw [hr2,hq]
        omega
      have hB2 : BB6.Agent3.CReach
          (3470+10944*u) (164585+518816*u) := by
        simpa only [hx,hy] using hB
      exact u5_q0_h40_B2_unreachable u hB2
    · have hpow3 := hpow
      rw [hr3] at hpow3
      norm_num at hpow3
      have hq : q=434+1368*u := by omega
      have hx : 2*q-2=866+2736*u := by rw [hq]; omega
      have hy :
          2487+4096*(40+128*u)-q-3*r=165884+522920*u := by
        rw [hr3,hq]
        omega
      have hB3 : BB6.Agent3.CReach
          (866+2736*u) (165884+522920*u) := by
        simpa only [hx,hy] using hB
      exact u5_q0_h40_B3_unreachable u hB3

#print axioms u5_q0_h40_E_unreachable
#print axioms u5_q0_h40_B1_unreachable
#print axioms u5_q0_h40_B2_unreachable
#print axioms u5_q0_h40_B3_unreachable
#print axioms u5_q0_secondary_parent_unreachable_h40

end BB6.Agent3U5Q0H40

import U5Q0SourceOnly
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-!
A source-only extension of the U5 odd/odd q-fan.

For t=123+168*z with z=256*v+2, the exact fan has only q=0,1.
Both parents are forced down finite, exact original-section predecessor
chains to already forbidden blank-image classes. This cylinder is not
one of the previously reported M16 or A/K64,C32 quotient cylinders.

This is a Lean draft. It has not yet been compiled with Lean 4.36.0-rc2.
-/

namespace BB6.Agent4U5SourceOnlyW1021
open BB6.Agent3
open BB6.Agent46

private theorem even_even_sum_two_reach_implies_direct
    (x y : Nat) (hx : 5 < x) (hxe : x%2=0)
    (hy : 6≤y) (hye : y%2=0) (hsum : (x+y)%4=2)
    (hr : CReach x y) :
    CReach (x+y-2) ((y-2)/2) := by
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  have hfan := BB6.Agent3ParentFan.even_even_parent_fan
    a k x y (by omega) hxe hy hye hstep
  rcases hfan with hdirect | hzero | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    simpa only [ha,hk] using hprev
  · rcases hzero with ⟨_,_,n,hxy,_⟩
    rw [hxy] at hsum
    omega
  · rcases hbounce with ⟨_,_,_,_,n,hn,hxy,_⟩
    have hdiv : 4∣2^(n+1) := by
      change 2^2∣2^(n+1)
      exact Nat.pow_dvd_pow 2 (by omega)
    have hpowmod : (2^(n+1))%4=0 :=
      Nat.mod_eq_zero_of_dvd hdiv
    have hmod : (2^(n+1)*(a+2))%4=0 := by
      simp [Nat.mul_mod,hpowmod]
    rw [hxy] at hsum
    omega

/-- If an even/even blank-reachable target has sum 4 modulo 8, the
complete source parent fan again forces its direct parent: the zero-left
and even-a bounce alternatives have sums divisible by 8. -/
private theorem even_even_sum_four_mod8_reach_implies_direct
    (x y : Nat) (hx : 5 < x) (hxe : x%2=0)
    (hy : 6≤y) (hye : y%2=0) (hsum : (x+y)%8=4)
    (hr : CReach x y) :
    CReach (x+y-2) ((y-2)/2) := by
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  have hfan := BB6.Agent3ParentFan.even_even_parent_fan
    a k x y (by omega) hxe hy hye hstep
  rcases hfan with hdirect | hzero | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    simpa only [ha,hk] using hprev
  · rcases hzero with ⟨_,_,n,hxy,_⟩
    rw [hxy] at hsum
    omega
  · rcases hbounce with ⟨_,haeven,_,_,n,hn,hxy,_⟩
    have hdiv4 : 4∣2^(n+1) := by
      change 2^2∣2^(n+1)
      exact Nat.pow_dvd_pow 2 (by omega)
    have hdiv2 : 2∣a+2 := by
      refine ⟨a/2+1,?_⟩
      omega
    obtain ⟨r,hr⟩ := hdiv4
    obtain ⟨s,hs⟩ := hdiv2
    have hdiv8 : 8∣2^(n+1)*(a+2) := by
      refine ⟨r*s,?_⟩
      rw [hr,hs]
      calc
        (4*r)*(2*s) = (4*2)*(r*s) := by ac_rfl
        _ = 8*(r*s) := by norm_num
    have hmod : (2^(n+1)*(a+2))%8=0 :=
      Nat.mod_eq_zero_of_dvd hdiv8
    rw [hxy] at hsum
    omega

/-- The exact U5 q-fan excludes X_t=(44t-1,42t-1) for
t=123+168*(256*v+2). The q=0 branch is reduced through
even/even -> even/odd -> odd/even -> odd/odd -> even/odd, ending in
odd-right sum one. The q=1 branch is reduced through
even/even -> even/even -> even/even -> even/odd -> odd/odd,
ending in odd/odd sum two. q>=2 is impossible modulo 16. -/
theorem q0_X_not_reach_t123_z2mod256 (v : Nat) :
    ¬ CReach
      (44*(123+168*(256*v+2))-1)
      (42*(123+168*(256*v+2))-1) := by
  let z := 256*v+2
  let t := 123+168*z
  intro hX
  have hX' : CReach (44*t-1) (42*t-1) := by
    simpa only [t,z] using hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*t-1) (42*t-1) (by dsimp [t,z]; omega) hX'
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
      t a k (by dsimp [t,z]; omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hNmod : (43*t-1)%16=8 := by
    dsimp [t,z]
    omega
  have hqle : q≤1 := by
    by_contra hq
    have hq2 : 2≤q := by omega
    have hdiv16 : 16∣4^q := by
      have h := Nat.pow_dvd_pow 4 hq2
      norm_num at h ⊢
      exact h
    obtain ⟨r,hr⟩ := hdiv16
    have hdivN : 16∣43*t-1 := by
      refine ⟨r*U,?_⟩
      rw [hpow,hr]
      ac_rfl
    have hzero : (43*t-1)%16=0 :=
      Nat.mod_eq_zero_of_dvd hdivN
    omega
  have hqcases : q=0 ∨ q=1 := by omega
  rcases hqcases with hq0 | hq1
  · subst q
    have hU0 : U=43*t-1 := by
      simpa using hpow.symm
    have ha0 : a=19734+1849344*v := by
      rw [hU0] at ha
      dsimp [t,z] at ha
      omega
    have hk0 : k=19504+1827840*v := by
      rw [hU0] at hcost
      dsimp [t,z] at hcost
      omega
    have hP0 : CReach
        (19734+1849344*v) (19504+1827840*v) := by
      simpa only [ha0,hk0] using hprev
    have hD0raw := even_even_sum_two_reach_implies_direct
      (19734+1849344*v) (19504+1827840*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP0
    have hD0 : CReach
        (39236+3677184*v) (9751+913920*v) := by
      have hx : (19734+1849344*v)+(19504+1827840*v)-2 =
          39236+3677184*v := by omega
      have hy : ((19504+1827840*v)-2)/2 =
          9751+913920*v := by omega
      simpa only [hx,hy] using hD0raw
    have hQ0run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (39236+3677184*v) (9751+913920*v)
      (by omega) (by omega) (by omega) (by omega)).mp hD0
    have hQ0 : CReach
        (24491+2295552*v) (17120+1604736*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (24491+2295552*v,17120+1604736*v))
      have hx : ((39236+3677184*v)+(9751+913920*v)-5)/2 =
          24491+2295552*v := by omega
      have hy : ((39236+3677184*v)+3*(9751+913920*v)-9)/4 =
          17120+1604736*v := by omega
      simpa only [hx,hy] using hQ0run
    have hR0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (24491+2295552*v) (17120+1604736*v)
      (by omega) (by omega) (by omega) (by omega)).mp hQ0
    have hR0 : CReach
        (41609+3900288*v) (8559+802368*v) := by
      have hx : (24491+2295552*v)+(17120+1604736*v)-2 =
          41609+3900288*v := by omega
      have hy : ((17120+1604736*v)-2)/2 =
          8559+802368*v := by omega
      simpa only [hx,hy] using hR0raw
    have hS0run := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (41609+3900288*v) (8559+802368*v)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hR0
    have hS0 : CReach
        (25082+2351328*v) (16819+1576848*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (25082+2351328*v,16819+1576848*v))
      have hx : ((41609+3900288*v)+(8559+802368*v)-4)/2 =
          25082+2351328*v := by omega
      have hy : ((41609+3900288*v)+3*(8559+802368*v)-10)/4 =
          16819+1576848*v := by omega
      simpa only [hx,hy] using hS0run
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (25082+2351328*v) (16819+1576848*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hS0
  · subst q
    have hU1 : 4*U=43*t-1 := by
      simpa using hpow.symm
    have hUval : U=4934+462336*v := by
      have hval : 43*t-1=4*(4934+462336*v) := by
        dsimp [t,z]
        omega
      omega
    have ha1 : a=4932+462336*v := by
      rw [hUval] at ha
      omega
    have hk1 : k=26902+2521344*v := by
      rw [hUval] at hcost
      omega
    have hP1 : CReach
        (4932+462336*v) (26902+2521344*v) := by
      simpa only [ha1,hk1] using hprev
    have hD1raw := even_even_sum_two_reach_implies_direct
      (4932+462336*v) (26902+2521344*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP1
    have hD1 : CReach
        (31832+2983680*v) (13450+1260672*v) := by
      have hx : (4932+462336*v)+(26902+2521344*v)-2 =
          31832+2983680*v := by omega
      have hy : ((26902+2521344*v)-2)/2 =
          13450+1260672*v := by omega
      simpa only [hx,hy] using hD1raw
    have hD2raw := even_even_sum_two_reach_implies_direct
      (31832+2983680*v) (13450+1260672*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD1
    have hD2 : CReach
        (45280+4244352*v) (6724+630336*v) := by
      have hx : (31832+2983680*v)+(13450+1260672*v)-2 =
          45280+4244352*v := by omega
      have hy : ((13450+1260672*v)-2)/2 =
          6724+630336*v := by omega
      simpa only [hx,hy] using hD2raw
    have hD3raw := even_even_sum_four_mod8_reach_implies_direct
      (45280+4244352*v) (6724+630336*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD2
    have hD3 : CReach
        (52002+4874688*v) (3361+315168*v) := by
      have hx : (45280+4244352*v)+(6724+630336*v)-2 =
          52002+4874688*v := by omega
      have hy : ((6724+630336*v)-2)/2 =
          3361+315168*v := by omega
      simpa only [hx,hy] using hD3raw
    have hQ3run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (52002+4874688*v) (3361+315168*v)
      (by omega) (by omega) (by omega) (by omega)).mp hD3
    have hQ3 : CReach
        (27679+2594928*v) (15519+1455048*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (27679+2594928*v,15519+1455048*v))
      have hx : ((52002+4874688*v)+(3361+315168*v)-5)/2 =
          27679+2594928*v := by omega
      have hy : ((52002+4874688*v)+3*(3361+315168*v)-9)/4 =
          15519+1455048*v := by omega
      simpa only [hx,hy] using hQ3run
    have hbad := BB6.Agent11High.blank_no_odd_sum_two
      (27679+2594928*v) (15519+1455048*v)
      (by omega) (by omega) (by omega)
    exact hbad hQ3

#print axioms even_even_sum_two_reach_implies_direct
#print axioms even_even_sum_four_mod8_reach_implies_direct
#print axioms q0_X_not_reach_t123_z2mod256

end BB6.Agent4U5SourceOnlyW1021

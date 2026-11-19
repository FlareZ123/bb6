import U5Q0SourceOnly
import HighEvenRightSum7Source
import HighSumTwo
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-!
A source-only extension of the U5 odd/odd q-fan.

For every t=459+1024*v, the exact fan has only q=0,1.
Both parents are forced down finite, exact original-section predecessor
chains to already forbidden blank-image classes. The older z=2 (mod 128)
parameterization is retained as a corollary wrapper.

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
        _ = 8*(r*s) := by rfl
    have hmod : (2^(n+1)*(a+2))%8=0 :=
      Nat.mod_eq_zero_of_dvd hdiv8
    rw [hxy] at hsum
    omega

/- The older z=2 (mod 128) parameterization is retained below as
a corollary of the stronger t=459 (mod 1024) theorem. -/
/-- The exact U5 q-fan excludes X_t for every t=459 (mod 1024).
The q=0 branch reaches odd-right sum one; q=1 reaches odd/odd sum
two. Since 43*t-1 is 8 (mod 16), q>=2 is impossible. -/
theorem q0_X_not_reach_t459mod1024 (v : Nat) :
    ¬ CReach
      (44*(459+1024*v)-1)
      (42*(459+1024*v)-1) := by
  let t := 459+1024*v
  intro hX
  have hX' : CReach (44*t-1) (42*t-1) := by
    simpa only [t] using hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*t-1) (42*t-1) (by dsimp [t]; omega) hX'
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
      t a k (by dsimp [t]; omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hNmod : (43*t-1)%16=8 := by
    dsimp [t]
    omega
  have hqle : q≤1 := by
    by_contra hq
    have hq2 : 2≤q := by omega
    have hdiv16 : 16∣4^q := by
      exact Nat.pow_dvd_pow 4 hq2
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
    have hU0 : U=43*t-1 := by simpa using hpow.symm
    have ha0 : a=19734+44032*v := by
      rw [hU0] at ha
      dsimp [t] at ha
      omega
    have hk0 : k=19504+43520*v := by
      rw [hU0] at hcost
      dsimp [t] at hcost
      omega
    have hP0 : CReach
        (19734+44032*v) (19504+43520*v) := by
      simpa only [ha0,hk0] using hprev
    have hD0raw := even_even_sum_two_reach_implies_direct
      (19734+44032*v) (19504+43520*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP0
    have hD0 : CReach
        (39236+87552*v) (9751+21760*v) := by
      have hx : (19734+44032*v)+(19504+43520*v)-2 =
          39236+87552*v := by omega
      have hy : ((19504+43520*v)-2)/2 =
          9751+21760*v := by omega
      simpa only [hx,hy] using hD0raw
    have hQ0run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (39236+87552*v) (9751+21760*v)
      (by omega) (by omega) (by omega) (by omega)).mp hD0
    have hQ0 : CReach
        (24491+54656*v) (17120+38208*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (24491+54656*v,17120+38208*v))
      have hx : ((39236+87552*v)+(9751+21760*v)-5)/2 =
          24491+54656*v := by omega
      have hy : ((39236+87552*v)+3*(9751+21760*v)-9)/4 =
          17120+38208*v := by omega
      simpa only [hx,hy] using hQ0run
    have hR0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (24491+54656*v) (17120+38208*v)
      (by omega) (by omega) (by omega) (by omega)).mp hQ0
    have hR0 : CReach
        (41609+92864*v) (8559+19104*v) := by
      have hx : (24491+54656*v)+(17120+38208*v)-2 =
          41609+92864*v := by omega
      have hy : ((17120+38208*v)-2)/2 =
          8559+19104*v := by omega
      simpa only [hx,hy] using hR0raw
    have hS0run := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (41609+92864*v) (8559+19104*v)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hR0
    have hS0 : CReach
        (25082+55984*v) (16819+37544*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (25082+55984*v,16819+37544*v))
      have hx : ((41609+92864*v)+(8559+19104*v)-4)/2 =
          25082+55984*v := by omega
      have hy : ((41609+92864*v)+3*(8559+19104*v)-10)/4 =
          16819+37544*v := by omega
      simpa only [hx,hy] using hS0run
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (25082+55984*v) (16819+37544*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hS0
  · subst q
    have hU1 : 4*U=43*t-1 := by simpa using hpow.symm
    have hUval : U=4934+11008*v := by
      have hval : 43*t-1=4*(4934+11008*v) := by
        dsimp [t]
        omega
      omega
    have ha1 : a=4932+11008*v := by
      rw [hUval] at ha
      omega
    have hk1 : k=26902+60032*v := by
      rw [hUval] at hcost
      dsimp [t] at hcost
      omega
    have hP1 : CReach
        (4932+11008*v) (26902+60032*v) := by
      simpa only [ha1,hk1] using hprev
    have hD1raw := even_even_sum_two_reach_implies_direct
      (4932+11008*v) (26902+60032*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP1
    have hD1 : CReach
        (31832+71040*v) (13450+30016*v) := by
      have hx : (4932+11008*v)+(26902+60032*v)-2 =
          31832+71040*v := by omega
      have hy : ((26902+60032*v)-2)/2 =
          13450+30016*v := by omega
      simpa only [hx,hy] using hD1raw
    have hD2raw := even_even_sum_two_reach_implies_direct
      (31832+71040*v) (13450+30016*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD1
    have hD2 : CReach
        (45280+101056*v) (6724+15008*v) := by
      have hx : (31832+71040*v)+(13450+30016*v)-2 =
          45280+101056*v := by omega
      have hy : ((13450+30016*v)-2)/2 =
          6724+15008*v := by omega
      simpa only [hx,hy] using hD2raw
    have hD3raw := even_even_sum_four_mod8_reach_implies_direct
      (45280+101056*v) (6724+15008*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD2
    have hD3 : CReach
        (52002+116064*v) (3361+7504*v) := by
      have hx : (45280+101056*v)+(6724+15008*v)-2 =
          52002+116064*v := by omega
      have hy : ((6724+15008*v)-2)/2 =
          3361+7504*v := by omega
      simpa only [hx,hy] using hD3raw
    have hQ3run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (52002+116064*v) (3361+7504*v)
      (by omega) (by omega) (by omega) (by omega)).mp hD3
    have hQ3 : CReach
        (27679+61784*v) (15519+34644*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (27679+61784*v,15519+34644*v))
      have hx : ((52002+116064*v)+(3361+7504*v)-5)/2 =
          27679+61784*v := by omega
      have hy : ((52002+116064*v)+3*(3361+7504*v)-9)/4 =
          15519+34644*v := by omega
      simpa only [hx,hy] using hQ3run
    have hbad := BB6.Agent11High.blank_no_odd_sum_two
      (27679+61784*v) (15519+34644*v)
      (by omega) (by omega) (by omega)
    exact hbad hQ3

/-- The previous z=2 (mod 128) statement is a special case of the
stronger t=459 (mod 1024) source exclusion. -/
theorem q0_X_not_reach_t123_z2mod128 (v : Nat) :
    ¬ CReach
      (44*(123+168*(128*v+2))-1)
      (42*(123+168*(128*v+2))-1) := by
  have ht : 123+168*(128*v+2)=459+1024*(21*v) := by omega
  simpa only [ht] using q0_X_not_reach_t459mod1024 (21*v)

/-- The exact U5 q-fan excludes X_t for every t=3875 (mod 4096).
The q=0 branch reaches odd-right sum one; q=1 and q=2 do likewise.
Since 43*t-1 is 96 (mod 128), q>=3 is impossible. -/
theorem q0_X_not_reach_t3875mod4096 (v : Nat) :
    ¬ CReach
      (44*(3875+4096*v)-1)
      (42*(3875+4096*v)-1) := by
  let t := 3875+4096*v
  intro hX
  have hX' : CReach (44*t-1) (42*t-1) := by
    simpa only [t] using hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*t-1) (42*t-1) (by dsimp [t]; omega) hX'
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
      t a k (by dsimp [t]; omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hNmod : (43*t-1)%128=96 := by
    dsimp [t]
    omega
  have hqle : q≤2 := by
    by_contra hq
    have hq3 : 3≤q := by omega
    have hdiv64 : 64∣4^q := by
      exact Nat.pow_dvd_pow 4 hq3
    have hdiv2 : 2∣U := by
      refine ⟨U/2,?_⟩
      omega
    obtain ⟨r,hr⟩ := hdiv64
    obtain ⟨s,hs⟩ := hdiv2
    have hdivN : 128∣43*t-1 := by
      refine ⟨r*s,?_⟩
      rw [hpow,hr,hs]
      ac_rfl
    have hzero : (43*t-1)%128=0 :=
      Nat.mod_eq_zero_of_dvd hdivN
    omega
  have hqcases : q=0 ∨ q=1 ∨ q=2 := by omega
  rcases hqcases with hq0 | hq1 | hq2
  · subst q
    have hU0 : U=43*t-1 := by simpa using hpow.symm
    have ha0 : a=166622+176128*v := by
      rw [hU0] at ha
      dsimp [t] at ha
      omega
    have hk0 : k=164684+174080*v := by
      rw [hU0] at hcost
      dsimp [t] at hcost
      omega
    have hP0 : CReach
        (166622+176128*v) (164684+174080*v) := by
      simpa only [ha0,hk0] using hprev
    have hD0raw := even_even_sum_two_reach_implies_direct
      (166622+176128*v) (164684+174080*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP0
    have hD0 : CReach
        (331304+350208*v) (82341+87040*v) := by
      have hx : (166622+176128*v)+(164684+174080*v)-2 =
          331304+350208*v := by omega
      have hy : ((164684+174080*v)-2)/2 =
          82341+87040*v := by omega
      simpa only [hx,hy] using hD0raw
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (331304+350208*v) (82341+87040*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hD0
  · subst q
    have hU1 : 4*U=43*t-1 := by simpa using hpow.symm
    have hUval : U=41656+44032*v := by
      have hval : 43*t-1=4*(41656+44032*v) := by
        dsimp [t]
        omega
      omega
    have ha1 : a=41654+44032*v := by
      rw [hUval] at ha
      omega
    have hk1 : k=227165+240128*v := by
      rw [hUval] at hcost
      dsimp [t] at hcost
      omega
    have hP1 : CReach
        (41654+44032*v) (227165+240128*v) := by
      simpa only [ha1,hk1] using hprev
    have hQ1run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (41654+44032*v) (227165+240128*v)
      (by omega) (by omega) (by omega) (by omega)).mp hP1
    have hQ1 : CReach
        (134407+142080*v) (180785+191104*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (134407+142080*v,180785+191104*v))
      have hx : ((41654+44032*v)+(227165+240128*v)-5)/2 =
          134407+142080*v := by omega
      have hy : ((41654+44032*v)+3*(227165+240128*v)-9)/4 =
          180785+191104*v := by omega
      simpa only [hx,hy] using hQ1run
    have hR1run := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (134407+142080*v) (180785+191104*v)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hQ1
    have hR1 : CReach
        (157594+166592*v) (169188+178848*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (157594+166592*v,169188+178848*v))
      have hx : ((134407+142080*v)+(180785+191104*v)-4)/2 =
          157594+166592*v := by omega
      have hy : ((134407+142080*v)+3*(180785+191104*v)-10)/4 =
          169188+178848*v := by omega
      simpa only [hx,hy] using hR1run
    have hD1raw := even_even_sum_two_reach_implies_direct
      (157594+166592*v) (169188+178848*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hR1
    have hD1 : CReach
        (326780+345440*v) (84593+89424*v) := by
      have hx : (157594+166592*v)+(169188+178848*v)-2 =
          326780+345440*v := by omega
      have hy : ((169188+178848*v)-2)/2 =
          84593+89424*v := by omega
      simpa only [hx,hy] using hD1raw
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (326780+345440*v) (84593+89424*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hD1
  · subst q
    have hU2 : 16*U=43*t-1 := by simpa using hpow.symm
    have hUval : U=10414+11008*v := by
      have hval : 43*t-1=16*(10414+11008*v) := by
        dsimp [t]
        omega
      omega
    have ha2 : a=10412+11008*v := by
      rw [hUval] at ha
      omega
    have hk2 : k=242783+256640*v := by
      rw [hUval] at hcost
      dsimp [t] at hcost
      omega
    have hP2 : CReach
        (10412+11008*v) (242783+256640*v) := by
      simpa only [ha2,hk2] using hprev
    have hQ2run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (10412+11008*v) (242783+256640*v)
      (by omega) (by omega) (by omega) (by omega)).mp hP2
    have hQ2 : CReach
        (126595+133824*v) (184688+195232*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (126595+133824*v,184688+195232*v))
      have hx : ((10412+11008*v)+(242783+256640*v)-5)/2 =
          126595+133824*v := by omega
      have hy : ((10412+11008*v)+3*(242783+256640*v)-9)/4 =
          184688+195232*v := by omega
      simpa only [hx,hy] using hQ2run
    have hR2run := (BB6.Agent46.six_even_right_blank_reach_iff
      (126595+133824*v) (184688+195232*v)
      (by omega) (by omega) (by omega) (by omega)).mp hQ2
    have hR2 : CReach
        (311281+329056*v) (92343+97616*v) := by
      have hx : (126595+133824*v)+(184688+195232*v)-2 =
          311281+329056*v := by omega
      have hy : ((184688+195232*v)-2)/2 =
          92343+97616*v := by omega
      simpa only [hx,hy] using hR2run
    have hS2run := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (311281+329056*v) (92343+97616*v)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hR2
    have hS2 : CReach
        (201810+213336*v) (147075+155476*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (201810+213336*v,147075+155476*v))
      have hx : ((311281+329056*v)+(92343+97616*v)-4)/2 =
          201810+213336*v := by omega
      have hy : ((311281+329056*v)+3*(92343+97616*v)-10)/4 =
          147075+155476*v := by omega
      simpa only [hx,hy] using hS2run
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (201810+213336*v) (147075+155476*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hS2

/-- The previous z=193 (mod 512) statement is a special case of the
stronger t=3875 (mod 4096) source exclusion. -/
theorem q0_X_not_reach_t123_z193mod512 (v : Nat) :
    ¬ CReach
      (44*(123+168*(512*v+193))-1)
      (42*(123+168*(512*v+193))-1) := by
  have ht : 123+168*(512*v+193)=3875+4096*(7+21*v) := by omega
  simpa only [ht] using q0_X_not_reach_t3875mod4096 (7+21*v)

/-- The exact U5 q-fan excludes X_t for every t=811 (mod 1024).
The q=0 branch reaches odd/odd sum two; q=1 reaches odd-right
sum one. Since 43*t-1 is 8 (mod 16), q>=2 is impossible. -/
theorem q0_X_not_reach_t811mod1024 (v : Nat) :
    ¬ CReach
      (44*(811+1024*v)-1)
      (42*(811+1024*v)-1) := by
  let t := 811+1024*v
  intro hX
  have hX' : CReach (44*t-1) (42*t-1) := by
    simpa only [t] using hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*t-1) (42*t-1) (by dsimp [t]; omega) hX'
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
      t a k (by dsimp [t]; omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hNmod : (43*t-1)%16=8 := by
    dsimp [t]
    omega
  have hqle : q≤1 := by
    by_contra hq
    have hq2 : 2≤q := by omega
    have hdiv16 : 16∣4^q := by
      exact Nat.pow_dvd_pow 4 hq2
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
    have hU0 : U=43*t-1 := by simpa using hpow.symm
    have ha0 : a=34870+44032*v := by
      rw [hU0] at ha
      dsimp [t] at ha
      omega
    have hk0 : k=34464+43520*v := by
      rw [hU0] at hcost
      dsimp [t] at hcost
      omega
    have hP0 : CReach
        (34870+44032*v) (34464+43520*v) := by
      simpa only [ha0,hk0] using hprev
    have hD0raw := even_even_sum_two_reach_implies_direct
      (34870+44032*v) (34464+43520*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP0
    have hD0 : CReach
        (69332+87552*v) (17231+21760*v) := by
      have hx : (34870+44032*v)+(34464+43520*v)-2 =
          69332+87552*v := by omega
      have hy : ((34464+43520*v)-2)/2 =
          17231+21760*v := by omega
      simpa only [hx,hy] using hD0raw
    have hQ0run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (69332+87552*v) (17231+21760*v)
      (by omega) (by omega) (by omega) (by omega)).mp hD0
    have hQ0 : CReach
        (43279+54656*v) (30254+38208*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (43279+54656*v,30254+38208*v))
      have hx : ((69332+87552*v)+(17231+21760*v)-5)/2 =
          43279+54656*v := by omega
      have hy : ((69332+87552*v)+3*(17231+21760*v)-9)/4 =
          30254+38208*v := by omega
      simpa only [hx,hy] using hQ0run
    have hR0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (43279+54656*v) (30254+38208*v)
      (by omega) (by omega) (by omega) (by omega)).mp hQ0
    have hR0 : CReach
        (73531+92864*v) (15126+19104*v) := by
      have hx : (43279+54656*v)+(30254+38208*v)-2 =
          73531+92864*v := by omega
      have hy : ((30254+38208*v)-2)/2 =
          15126+19104*v := by omega
      simpa only [hx,hy] using hR0raw
    have hS0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (73531+92864*v) (15126+19104*v)
      (by omega) (by omega) (by omega) (by omega)).mp hR0
    have hS0 : CReach
        (88655+111968*v) (7562+9552*v) := by
      have hx : (73531+92864*v)+(15126+19104*v)-2 =
          88655+111968*v := by omega
      have hy : ((15126+19104*v)-2)/2 =
          7562+9552*v := by omega
      simpa only [hx,hy] using hS0raw
    have hT0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (88655+111968*v) (7562+9552*v)
      (by omega) (by omega) (by omega) (by omega)).mp hS0
    have hT0 : CReach
        (96215+121520*v) (3780+4776*v) := by
      have hx : (88655+111968*v)+(7562+9552*v)-2 =
          96215+121520*v := by omega
      have hy : ((7562+9552*v)-2)/2 =
          3780+4776*v := by omega
      simpa only [hx,hy] using hT0raw
    have hU0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (96215+121520*v) (3780+4776*v)
      (by omega) (by omega) (by omega) (by omega)).mp hT0
    have hU0reach : CReach
        (99993+126296*v) (1889+2388*v) := by
      have hx : (96215+121520*v)+(3780+4776*v)-2 =
          99993+126296*v := by omega
      have hy : ((3780+4776*v)-2)/2 =
          1889+2388*v := by omega
      simpa only [hx,hy] using hU0raw
    have hbad := BB6.Agent11High.blank_no_odd_sum_two
      (99993+126296*v) (1889+2388*v)
      (by omega) (by omega) (by omega)
    exact hbad hU0reach
  · subst q
    have hU1 : 4*U=43*t-1 := by simpa using hpow.symm
    have hUval : U=8718+11008*v := by
      have hval : 43*t-1=4*(8718+11008*v) := by
        dsimp [t]
        omega
      omega
    have ha1 : a=8716+11008*v := by
      rw [hUval] at ha
      omega
    have hk1 : k=47538+60032*v := by
      rw [hUval] at hcost
      dsimp [t] at hcost
      omega
    have hP1 : CReach
        (8716+11008*v) (47538+60032*v) := by
      simpa only [ha1,hk1] using hprev
    have hD1raw := even_even_sum_two_reach_implies_direct
      (8716+11008*v) (47538+60032*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP1
    have hD1 : CReach
        (56252+71040*v) (23768+30016*v) := by
      have hx : (8716+11008*v)+(47538+60032*v)-2 =
          56252+71040*v := by omega
      have hy : ((47538+60032*v)-2)/2 =
          23768+30016*v := by omega
      simpa only [hx,hy] using hD1raw
    have hD2raw := even_even_sum_four_mod8_reach_implies_direct
      (56252+71040*v) (23768+30016*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD1
    have hD2 : CReach
        (80018+101056*v) (11883+15008*v) := by
      have hx : (56252+71040*v)+(23768+30016*v)-2 =
          80018+101056*v := by omega
      have hy : ((23768+30016*v)-2)/2 =
          11883+15008*v := by omega
      simpa only [hx,hy] using hD2raw
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (80018+101056*v) (11883+15008*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hD2

/-- The previous z=126 (mod 128) statement is a special case of the
stronger t=811 (mod 1024) source exclusion. -/
theorem q0_X_not_reach_t123_z126mod128 (v : Nat) :
    ¬ CReach
      (44*(123+168*(128*v+126))-1)
      (42*(123+168*(128*v+126))-1) := by
  have ht : 123+168*(128*v+126)=811+1024*(20+21*v) := by omega
  simpa only [ht] using q0_X_not_reach_t811mod1024 (20+21*v)

#print axioms q0_X_not_reach_t459mod1024
#print axioms q0_X_not_reach_t123_z2mod128
#print axioms q0_X_not_reach_t3875mod4096
#print axioms q0_X_not_reach_t123_z193mod512
#print axioms q0_X_not_reach_t811mod1024
#print axioms q0_X_not_reach_t123_z126mod128





/-- A stronger exact q=0 source-only exclusion.  The t=1707 (mod 2048)
class has only q=0,1 in the complete original-source parent fan. Both
branches descend by forced source inverses to the established odd-image
forbidden class. -/
theorem q0_X_not_reach_t1707mod2048 (v : Nat) :
    ¬ CReach
      (44*(1707+2048*v)-1)
      (42*(1707+2048*v)-1) := by
  let t := 1707+2048*v
  intro hX
  have hX' : CReach (44*t-1) (42*t-1) := by
    simpa only [t] using hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*t-1) (42*t-1) (by dsimp [t]; omega) hX'
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
      t a k (by dsimp [t]; omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hNmod : (43*t-1)%16=8 := by
    dsimp [t]
    omega
  have hqle : q≤1 := by
    by_contra hq
    have hq2 : 2≤q := by omega
    have hdiv16 : 16∣4^q := by
      exact Nat.pow_dvd_pow 4 hq2
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
    have hU0 : U=43*t-1 := by simpa using hpow.symm
    have ha0 : a=73398+88064*v := by
      rw [hU0] at ha
      dsimp [t] at ha
      omega
    have hk0 : k=72544+87040*v := by
      rw [hU0] at hcost
      dsimp [t] at hcost
      omega
    have hP0 : CReach
        (73398+88064*v) (72544+87040*v) := by
      simpa only [ha0,hk0] using hprev
    have hD0raw := even_even_sum_two_reach_implies_direct
      (73398+88064*v) (72544+87040*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP0
    have hD0 : CReach
        (145940+175104*v) (36271+43520*v) := by
      have hx : (73398+88064*v)+(72544+87040*v)-2 =
          145940+175104*v := by omega
      have hy : ((72544+87040*v)-2)/2 =
          36271+43520*v := by omega
      simpa only [hx,hy] using hD0raw
    have hQ0run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (145940+175104*v) (36271+43520*v)
      (by omega) (by omega) (by omega) (by omega)).mp hD0
    have hQ0 : CReach
        (91103+109312*v) (63686+76416*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (91103+109312*v,63686+76416*v))
      have hx : ((145940+175104*v)+(36271+43520*v)-5)/2 =
          91103+109312*v := by omega
      have hy : ((145940+175104*v)+3*(36271+43520*v)-9)/4 =
          63686+76416*v := by omega
      simpa only [hx,hy] using hQ0run
    have hR1raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (91103+109312*v) (63686+76416*v)
      (by omega) (by omega) (by omega) (by omega)).mp hQ0
    have hR1 : CReach
        (154787+185728*v) (31842+38208*v) := by
      have hx : (91103+109312*v)+(63686+76416*v)-2 =
          154787+185728*v := by omega
      have hy : ((63686+76416*v)-2)/2 =
          31842+38208*v := by omega
      simpa only [hx,hy] using hR1raw
    have hR2raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (154787+185728*v) (31842+38208*v)
      (by omega) (by omega) (by omega) (by omega)).mp hR1
    have hR2 : CReach
        (186627+223936*v) (15920+19104*v) := by
      have hx : (154787+185728*v)+(31842+38208*v)-2 =
          186627+223936*v := by omega
      have hy : ((31842+38208*v)-2)/2 =
          15920+19104*v := by omega
      simpa only [hx,hy] using hR2raw
    have hR3raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (186627+223936*v) (15920+19104*v)
      (by omega) (by omega) (by omega) (by omega)).mp hR2
    have hR3 : CReach
        (202545+243040*v) (7959+9552*v) := by
      have hx : (186627+223936*v)+(15920+19104*v)-2 =
          202545+243040*v := by omega
      have hy : ((15920+19104*v)-2)/2 =
          7959+9552*v := by omega
      simpa only [hx,hy] using hR3raw
    have hS0run := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (202545+243040*v) (7959+9552*v)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hR3
    have hS0 : CReach
        (105250+126296*v) (56603+67924*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (105250+126296*v,56603+67924*v))
      have hx : ((202545+243040*v)+(7959+9552*v)-4)/2 =
          105250+126296*v := by omega
      have hy : ((202545+243040*v)+3*(7959+9552*v)-10)/4 =
          56603+67924*v := by omega
      simpa only [hx,hy] using hS0run
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (105250+126296*v) (56603+67924*v)
      (by omega) (by omega) (by omega) (by omega) hS0
  · subst q
    have hU1 : 4*U=43*t-1 := by simpa using hpow.symm
    have hUval : U=18350+22016*v := by
      have hval : 43*t-1=4*(18350+22016*v) := by
        dsimp [t]
        omega
      omega
    have ha1 : a=18348+22016*v := by
      rw [hUval] at ha
      omega
    have hk1 : k=100066+120064*v := by
      rw [hUval] at hcost
      dsimp [t] at hcost
      omega
    have hP1 : CReach
        (18348+22016*v) (100066+120064*v) := by
      simpa only [ha1,hk1] using hprev
    have hD1raw := even_even_sum_two_reach_implies_direct
      (18348+22016*v) (100066+120064*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP1
    have hD1 : CReach
        (118412+142080*v) (50032+60032*v) := by
      have hx : (18348+22016*v)+(100066+120064*v)-2 =
          118412+142080*v := by omega
      have hy : ((100066+120064*v)-2)/2 =
          50032+60032*v := by omega
      simpa only [hx,hy] using hD1raw
    have hD2raw := even_even_sum_four_mod8_reach_implies_direct
      (118412+142080*v) (50032+60032*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD1
    have hD2 : CReach
        (168442+202112*v) (25015+30016*v) := by
      have hx : (118412+142080*v)+(50032+60032*v)-2 =
          168442+202112*v := by omega
      have hy : ((50032+60032*v)-2)/2 =
          25015+30016*v := by omega
      simpa only [hx,hy] using hD2raw
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (168442+202112*v) (25015+30016*v)
      (by omega) (by omega) (by omega) (by omega) hD2

#print axioms q0_X_not_reach_t1707mod2048



/-- A sum-seven target cylinder is also blank-unreachable: the complete
SectionAllInverse grammar sends every possible parent into the forbidden
odd/odd sum-two image. -/
private theorem blank_no_sum7_target (x y : Nat)
    (hx : 5<x) (hy12 : 12≤y) (hxy8 : (x+y)%8=7)
    (hS16 : (x+y+1)%16=8) (hS32 : (x+y+1)%32=24)
    (hx4 : x%4=3) (hy8 : y%8=4) :
    ¬ CReach x y := by
  intro hreach
  obtain ⟨a,b,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      x y hx hreach
  have hpre : BB6.Agent46.sectionPreimageAll a b x y :=
    (BB6.Agent46.section_preimage_all_iff a b x y).mp hstep
  have himage := BB6.Agent19HighEvenRight.sum7_every_parent_odd_image
    x y a b hy12 hxy8 hS16 hS32 hx4 hy8 hpre
  exact BB6.Agent11High.blank_no_odd_sum_two
    a b himage.1 himage.2.1 himage.2.2 hprev

/-- A second q-fan source-only cylinder. The q=0 branch terminates in
the exact sum-seven parent fan; q=1 descends through six forced even/even
parents to the odd-right sum-one forbidden class. -/
theorem q0_X_not_reach_t1547mod2048 (v : Nat) :
    ¬ CReach
      (44*(1547+2048*v)-1)
      (42*(1547+2048*v)-1) := by
  let t := 1547+2048*v
  intro hX
  have hX' : CReach (44*t-1) (42*t-1) := by
    simpa only [t] using hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*t-1) (42*t-1) (by dsimp [t]; omega) hX'
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
      t a k (by dsimp [t]; omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hNmod : (43*t-1)%16=8 := by
    dsimp [t]
    omega
  have hqle : q≤1 := by
    by_contra hq
    have hq2 : 2≤q := by omega
    have hdiv16 : 16∣4^q := by
      exact Nat.pow_dvd_pow 4 hq2
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
    have hU0 : U=43*t-1 := by simpa using hpow.symm
    have ha0 : a=66518+88064*v := by
      rw [hU0] at ha
      dsimp [t] at ha
      omega
    have hk0 : k=65744+87040*v := by
      rw [hU0] at hcost
      dsimp [t] at hcost
      omega
    have hP0 : CReach
        (66518+88064*v) (65744+87040*v) := by
      simpa only [ha0,hk0] using hprev
    have hD0raw := even_even_sum_two_reach_implies_direct
      (66518+88064*v) (65744+87040*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP0
    have hD0 : CReach
        (132260+175104*v) (32871+43520*v) := by
      have hx : (66518+88064*v)+(65744+87040*v)-2 =
          132260+175104*v := by omega
      have hy : ((65744+87040*v)-2)/2 =
          32871+43520*v := by omega
      simpa only [hx,hy] using hD0raw
    have hQ0run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (132260+175104*v) (32871+43520*v)
      (by omega) (by omega) (by omega) (by omega)).mp hD0
    have hQ0 : CReach
        (82563+109312*v) (57716+76416*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (82563+109312*v,57716+76416*v))
      have hx : ((132260+175104*v)+(32871+43520*v)-5)/2 =
          82563+109312*v := by omega
      have hy : ((132260+175104*v)+3*(32871+43520*v)-9)/4 =
          57716+76416*v := by omega
      simpa only [hx,hy] using hQ0run
    exact blank_no_sum7_target
      (82563+109312*v) (57716+76416*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hQ0
  · subst q
    have hU1 : 4*U=43*t-1 := by simpa using hpow.symm
    have hUval : U=16630+22016*v := by
      have hval : 43*t-1=4*(16630+22016*v) := by
        dsimp [t]
        omega
      omega
    have ha1 : a=16628+22016*v := by
      rw [hUval] at ha
      omega
    have hk1 : k=90686+120064*v := by
      rw [hUval] at hcost
      dsimp [t] at hcost
      omega
    have hP1 : CReach
        (16628+22016*v) (90686+120064*v) := by
      simpa only [ha1,hk1] using hprev
    have hD1raw := even_even_sum_two_reach_implies_direct
      (16628+22016*v) (90686+120064*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP1
    have hD1 : CReach
        (107312+142080*v) (45342+60032*v) := by
      have hx : (16628+22016*v)+(90686+120064*v)-2 =
          107312+142080*v := by omega
      have hy : ((90686+120064*v)-2)/2 =
          45342+60032*v := by omega
      simpa only [hx,hy] using hD1raw
    have hD2raw := even_even_sum_two_reach_implies_direct
      (107312+142080*v) (45342+60032*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD1
    have hD2 : CReach
        (152652+202112*v) (22670+30016*v) := by
      have hx : (107312+142080*v)+(45342+60032*v)-2 =
          152652+202112*v := by omega
      have hy : ((45342+60032*v)-2)/2 =
          22670+30016*v := by omega
      simpa only [hx,hy] using hD2raw
    have hD3raw := even_even_sum_two_reach_implies_direct
      (152652+202112*v) (22670+30016*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD2
    have hD3 : CReach
        (175320+232128*v) (11334+15008*v) := by
      have hx : (152652+202112*v)+(22670+30016*v)-2 =
          175320+232128*v := by omega
      have hy : ((22670+30016*v)-2)/2 =
          11334+15008*v := by omega
      simpa only [hx,hy] using hD3raw
    have hD4raw := even_even_sum_two_reach_implies_direct
      (175320+232128*v) (11334+15008*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD3
    have hD4 : CReach
        (186652+247136*v) (5666+7504*v) := by
      have hx : (175320+232128*v)+(11334+15008*v)-2 =
          186652+247136*v := by omega
      have hy : ((11334+15008*v)-2)/2 =
          5666+7504*v := by omega
      simpa only [hx,hy] using hD4raw
    have hD5raw := even_even_sum_two_reach_implies_direct
      (186652+247136*v) (5666+7504*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD4
    have hD5 : CReach
        (192316+254640*v) (2832+3752*v) := by
      have hx : (186652+247136*v)+(5666+7504*v)-2 =
          192316+254640*v := by omega
      have hy : ((5666+7504*v)-2)/2 =
          2832+3752*v := by omega
      simpa only [hx,hy] using hD5raw
    have hD6raw := even_even_sum_four_mod8_reach_implies_direct
      (192316+254640*v) (2832+3752*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD5
    have hD6 : CReach
        (195146+258392*v) (1415+1876*v) := by
      have hx : (192316+254640*v)+(2832+3752*v)-2 =
          195146+258392*v := by omega
      have hy : ((2832+3752*v)-2)/2 =
          1415+1876*v := by omega
      simpa only [hx,hy] using hD6raw
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (195146+258392*v) (1415+1876*v)
      (by omega) (by omega) (by omega) (by omega) hD6

#print axioms blank_no_sum7_target
#print axioms q0_X_not_reach_t1547mod2048

end BB6.Agent4U5SourceOnlyW1021

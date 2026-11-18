import U5Q0SourceOnly
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-!
A source-only extension of the U5 odd/odd q-fan.

For t=123+168*z with z=128*v+2, the exact fan has only q=0,1.
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
t=123+168*(128*v+2). The q=0 branch is reduced through
even/even -> even/odd -> odd/even -> odd/odd -> even/odd, ending in
odd-right sum one. The q=1 branch is reduced through
even/even -> even/even -> even/even -> even/odd -> odd/odd,
ending in odd/odd sum two. q>=2 is impossible modulo 16. -/
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

/-- The exact U5 q-fan excludes X_t for z=512*v+193.
The q=0 parent reaches odd-right sum one directly; q=1 reaches it
through even/odd-four, odd/odd valuation three, and even/even sum two;
q=2 reaches it through even/odd-four, six-even-right, and odd/odd
valuation three. q>=3 is impossible modulo 128. -/
theorem q0_X_not_reach_t123_z193mod512 (v : Nat) :
    ¬ CReach
      (44*(123+168*(512*v+193))-1)
      (42*(123+168*(512*v+193))-1) := by
  let z := 512*v+193
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
  have hNmod : (43*t-1)%128=96 := by
    dsimp [t,z]
    omega
  have hqle : q≤2 := by
    by_contra hq
    have hq3 : 3≤q := by omega
    have h64 : 64∣4^q := by
      have h := Nat.pow_dvd_pow 4 hq3
      norm_num at h ⊢
      exact h
    have h2 : 2∣U := by
      refine ⟨U/2,?_⟩
      omega
    obtain ⟨r,hr⟩ := h64
    obtain ⟨s,hs⟩ := h2
    have h128 : 128∣4^q*U := by
      refine ⟨r*s,?_⟩
      rw [hr,hs]
      calc
        (64*r)*(2*s) = (64*2)*(r*s) := by ac_rfl
        _ = 128*(r*s) := by norm_num
    obtain ⟨r,hr⟩ := h128
    have hdiv : 128∣43*t-1 := by
      refine ⟨r,?_⟩
      rw [hpow]
      exact hr
    have hzero : (43*t-1)%128=0 :=
      Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hqcases : q=0 ∨ q=1 ∨ q=2 := by omega
  rcases hqcases with hq0 | hq1 | hq2
  · subst q
    have hU0 : U=43*t-1 := by simpa using hpow.symm
    have ha0 : a=1399518+3698688*v := by
      rw [hU0] at ha
      dsimp [t,z] at ha
      omega
    have hk0 : k=1383244+3655680*v := by
      rw [hU0] at hcost
      dsimp [t,z] at hcost
      omega
    have hP0 : CReach
        (1399518+3698688*v) (1383244+3655680*v) := by
      simpa only [ha0,hk0] using hprev
    have hD0raw := even_even_sum_two_reach_implies_direct
      (1399518+3698688*v) (1383244+3655680*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP0
    have hD0 : CReach
        (2782760+7354368*v) (691621+1827840*v) := by
      have hx : (1399518+3698688*v)+(1383244+3655680*v)-2 =
          2782760+7354368*v := by omega
      have hy : ((1383244+3655680*v)-2)/2 =
          691621+1827840*v := by omega
      simpa only [hx,hy] using hD0raw
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (2782760+7354368*v) (691621+1827840*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hD0
  · subst q
    have hU1 : 4*U=43*t-1 := by simpa using hpow.symm
    have hUval : U=349880+924672*v := by
      have hval : 43*t-1=4*(349880+924672*v) := by
        dsimp [t,z]
        omega
      omega
    have ha1 : a=349878+924672*v := by
      rw [hUval] at ha
      omega
    have hk1 : k=1908061+5042688*v := by
      rw [hUval] at hcost
      dsimp [t,z] at hcost
      omega
    have hP1 : CReach
        (349878+924672*v) (1908061+5042688*v) := by
      simpa only [ha1,hk1] using hprev
    have hQ1run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (349878+924672*v) (1908061+5042688*v)
      (by omega) (by omega) (by omega) (by omega)).mp hP1
    have hQ1 : CReach
        (1128967+2983680*v) (1518513+4013184*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (1128967+2983680*v,1518513+4013184*v))
      have hx : ((349878+924672*v)+(1908061+5042688*v)-5)/2 =
          1128967+2983680*v := by omega
      have hy : ((349878+924672*v)+3*(1908061+5042688*v)-9)/4 =
          1518513+4013184*v := by omega
      simpa only [hx,hy] using hQ1run
    have hR1run := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (1128967+2983680*v) (1518513+4013184*v)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hQ1
    have hR1 : CReach
        (1323738+3498432*v) (1421124+3755808*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (1323738+3498432*v,1421124+3755808*v))
      have hx : ((1128967+2983680*v)+(1518513+4013184*v)-4)/2 =
          1323738+3498432*v := by omega
      have hy : ((1128967+2983680*v)+3*(1518513+4013184*v)-10)/4 =
          1421124+3755808*v := by omega
      simpa only [hx,hy] using hR1run
    have hD1raw := even_even_sum_two_reach_implies_direct
      (1323738+3498432*v) (1421124+3755808*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hR1
    have hD1 : CReach
        (2744860+7254240*v) (710561+1877904*v) := by
      have hx : (1323738+3498432*v)+(1421124+3755808*v)-2 =
          2744860+7254240*v := by omega
      have hy : ((1421124+3755808*v)-2)/2 =
          710561+1877904*v := by omega
      simpa only [hx,hy] using hD1raw
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (2744860+7254240*v) (710561+1877904*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hD1
  · subst q
    have hU2 : 16*U=43*t-1 := by simpa using hpow.symm
    have hUval : U=87470+231168*v := by
      have hval : 43*t-1=16*(87470+231168*v) := by
        dsimp [t,z]
        omega
      omega
    have ha2 : a=87468+231168*v := by
      rw [hUval] at ha
      omega
    have hk2 : k=2039263+5389440*v := by
      rw [hUval] at hcost
      dsimp [t,z] at hcost
      omega
    have hP2 : CReach
        (87468+231168*v) (2039263+5389440*v) := by
      simpa only [ha2,hk2] using hprev
    have hQ2run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (87468+231168*v) (2039263+5389440*v)
      (by omega) (by omega) (by omega) (by omega)).mp hP2
    have hQ2 : CReach
        (1063363+2810304*v) (1551312+4099872*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (1063363+2810304*v,1551312+4099872*v))
      have hx : ((87468+231168*v)+(2039263+5389440*v)-5)/2 =
          1063363+2810304*v := by omega
      have hy : ((87468+231168*v)+3*(2039263+5389440*v)-9)/4 =
          1551312+4099872*v := by omega
      simpa only [hx,hy] using hQ2run
    have hR2raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (1063363+2810304*v) (1551312+4099872*v)
      (by omega) (by omega) (by omega) (by omega)).mp hQ2
    have hR2 : CReach
        (2614673+6910176*v) (775655+2049936*v) := by
      have hx : (1063363+2810304*v)+(1551312+4099872*v)-2 =
          2614673+6910176*v := by omega
      have hy : ((1551312+4099872*v)-2)/2 =
          775655+2049936*v := by omega
      simpa only [hx,hy] using hR2raw
    have hS2run := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (2614673+6910176*v) (775655+2049936*v)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hR2
    have hS2 : CReach
        (1695162+4480056*v) (1235407+3264996*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (1695162+4480056*v,1235407+3264996*v))
      have hx : ((2614673+6910176*v)+(775655+2049936*v)-4)/2 =
          1695162+4480056*v := by omega
      have hy : ((2614673+6910176*v)+3*(775655+2049936*v)-10)/4 =
          1235407+3264996*v := by omega
      simpa only [hx,hy] using hS2run
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (1695162+4480056*v) (1235407+3264996*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hS2

/-- The exact U5 q-fan excludes X_t for z=128*v+126.
The q=0 branch follows a direct even/even parent, one even/odd-four
parent, and four six-even-right parents to odd-right sum two. The q=1
branch follows two even/even direct parents to odd-right sum one.
q>=2 is impossible modulo 16. -/
theorem q0_X_not_reach_t123_z126mod128 (v : Nat) :
    ¬ CReach
      (44*(123+168*(128*v+126))-1)
      (42*(123+168*(128*v+126))-1) := by
  let z := 128*v+126
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
    have h16 : 16∣4^q := by
      have h := Nat.pow_dvd_pow 4 hq2
      norm_num at h ⊢
      exact h
    have h2 : 2∣U := by
      refine ⟨U/2,?_⟩
      omega
    obtain ⟨r,hr⟩ := h16
    obtain ⟨s,hs⟩ := h2
    have h32 : 32∣4^q*U := by
      refine ⟨r*s,?_⟩
      rw [hr,hs]
      calc
        (16*r)*(2*s) = (16*2)*(r*s) := by ac_rfl
        _ = 32*(r*s) := by norm_num
    obtain ⟨r,hr⟩ := h32
    have hdiv16 : 16∣43*t-1 := by
      refine ⟨2*r,?_⟩
      rw [hpow,hr]
      norm_num
    have hzero : (43*t-1)%16=0 :=
      Nat.mod_eq_zero_of_dvd hdiv16
    omega
  have hqcases : q=0 ∨ q=1 := by omega
  rcases hqcases with hq0 | hq1
  · subst q
    have hU0 : U=43*t-1 := by simpa using hpow.symm
    have ha0 : a=915510+924672*v := by
      rw [hU0] at ha
      dsimp [t,z] at ha
      omega
    have hk0 : k=904864+913920*v := by
      rw [hU0] at hcost
      dsimp [t,z] at hcost
      omega
    have hP0 : CReach
        (915510+924672*v) (904864+913920*v) := by
      simpa only [ha0,hk0] using hprev
    have hD0raw := even_even_sum_two_reach_implies_direct
      (915510+924672*v) (904864+913920*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP0
    have hD0 : CReach
        (1820372+1838592*v) (452431+456960*v) := by
      have hx : (915510+924672*v)+(904864+913920*v)-2 =
          1820372+1838592*v := by omega
      have hy : ((904864+913920*v)-2)/2 =
          452431+456960*v := by omega
      simpa only [hx,hy] using hD0raw
    have hQ0run := (BB6.Agent3.evenodd_four_blank_reach_iff
      (1820372+1838592*v) (452431+456960*v)
      (by omega) (by omega) (by omega) (by omega)).mp hD0
    have hQ0 : CReach
        (1136399+1147776*v) (794414+802368*v) := by
      change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
        (some (5,1)) = some
        (1136399+1147776*v,794414+802368*v))
      have hx : ((1820372+1838592*v)+(452431+456960*v)-5)/2 =
          1136399+1147776*v := by omega
      have hy : ((1820372+1838592*v)+3*(452431+456960*v)-9)/4 =
          794414+802368*v := by omega
      simpa only [hx,hy] using hQ0run
    have hR0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (1136399+1147776*v) (794414+802368*v)
      (by omega) (by omega) (by omega) (by omega)).mp hQ0
    have hR0 : CReach
        (1930811+1950144*v) (397206+401184*v) := by
      have hx : (1136399+1147776*v)+(794414+802368*v)-2 =
          1930811+1950144*v := by omega
      have hy : ((794414+802368*v)-2)/2 =
          397206+401184*v := by omega
      simpa only [hx,hy] using hR0raw
    have hS0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (1930811+1950144*v) (397206+401184*v)
      (by omega) (by omega) (by omega) (by omega)).mp hR0
    have hS0 : CReach
        (2328015+2351328*v) (198602+200592*v) := by
      have hx : (1930811+1950144*v)+(397206+401184*v)-2 =
          2328015+2351328*v := by omega
      have hy : ((397206+401184*v)-2)/2 =
          198602+200592*v := by omega
      simpa only [hx,hy] using hS0raw
    have hT0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (2328015+2351328*v) (198602+200592*v)
      (by omega) (by omega) (by omega) (by omega)).mp hS0
    have hT0 : CReach
        (2526615+2551920*v) (99300+100296*v) := by
      have hx : (2328015+2351328*v)+(198602+200592*v)-2 =
          2526615+2551920*v := by omega
      have hy : ((198602+200592*v)-2)/2 =
          99300+100296*v := by omega
      simpa only [hx,hy] using hT0raw
    have hU0raw := (BB6.Agent46.six_even_right_blank_reach_iff
      (2526615+2551920*v) (99300+100296*v)
      (by omega) (by omega) (by omega) (by omega)).mp hT0
    have hV0 : CReach
        (2625913+2652216*v) (49649+50148*v) := by
      have hx : (2526615+2551920*v)+(99300+100296*v)-2 =
          2625913+2652216*v := by omega
      have hy : ((99300+100296*v)-2)/2 =
          49649+50148*v := by omega
      simpa only [hx,hy] using hU0raw
    have hbad := BB6.Agent11High.blank_no_odd_sum_two
      (2625913+2652216*v) (49649+50148*v)
      (by omega) (by omega) (by omega)
    exact hbad hV0
  · subst q
    have hU1 : 4*U=43*t-1 := by simpa using hpow.symm
    have hUval : U=228878+231168*v := by
      have hval : 43*t-1=4*(228878+231168*v) := by
        dsimp [t,z]
        omega
      omega
    have ha1 : a=228876+231168*v := by
      rw [hUval] at ha
      omega
    have hk1 : k=1248178+1260672*v := by
      rw [hUval] at hcost
      dsimp [t,z] at hcost
      omega
    have hP1 : CReach
        (228876+231168*v) (1248178+1260672*v) := by
      simpa only [ha1,hk1] using hprev
    have hD1raw := even_even_sum_two_reach_implies_direct
      (228876+231168*v) (1248178+1260672*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hP1
    have hD1 : CReach
        (1477052+1491840*v) (624088+630336*v) := by
      have hx : (228876+231168*v)+(1248178+1260672*v)-2 =
          1477052+1491840*v := by omega
      have hy : ((1248178+1260672*v)-2)/2 =
          624088+630336*v := by omega
      simpa only [hx,hy] using hD1raw
    have hD2raw := even_even_sum_four_mod8_reach_implies_direct
      (1477052+1491840*v) (624088+630336*v)
      (by omega) (by omega) (by omega) (by omega) (by omega) hD1
    have hD2 : CReach
        (2101138+2122176*v) (312043+315168*v) := by
      have hx : (1477052+1491840*v)+(624088+630336*v)-2 =
          2101138+2122176*v := by omega
      have hy : ((624088+630336*v)-2)/2 =
          312043+315168*v := by omega
      simpa only [hx,hy] using hD2raw
    have hbad := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (2101138+2122176*v) (312043+315168*v)
      (by omega) (by omega) (by omega) (by omega)
    exact hbad hD2

#print axioms even_even_sum_two_reach_implies_direct
#print axioms even_even_sum_four_mod8_reach_implies_direct
#print axioms q0_X_not_reach_t459mod1024
#print axioms q0_X_not_reach_t123_z2mod128
#print axioms q0_X_not_reach_t123_z193mod512
#print axioms q0_X_not_reach_t123_z126mod128

end BB6.Agent4U5SourceOnlyW1021

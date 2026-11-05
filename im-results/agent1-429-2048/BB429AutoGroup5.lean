import BB429RootMod32
import BB429NewResidue
import Lean.Elab.Tactic.Omega

namespace BB429AutoGroup5
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

private theorem no_585_11 (q : Nat) :
    ¬ Reach (2720*q+760) (2752*q+781) := by
  intro hr
  have ha := reach_allowed (2720*q+760) (2752*q+781) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_585_10 (q : Nat) :
    ¬ Reach (1108*q+308) (5976*q+1680) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (1108*q+308) (5976*q+1680) hn (by omega) (by omega)
  omega

private theorem no_585_9 (q : Nat) :
    ¬ Reach (2216*q+619) (3760*q+1061) := by
  intro hr
  rcases odd_back (2216*q+619) (3760*q+1061) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1108*q+308 := by omega
    have ye : y = 5976*q+1680 := by omega
    rw [xe,ye] at hp
    exact no_585_10 q hp
  · omega

private theorem no_585_8 (q : Nat) :
    ¬ Reach (336*q+92) (7520*q+2122) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (336*q+92) (7520*q+2122) (by omega) (by omega) hr
  have xe : x = 2216*q+619 := by omega
  have ye : y = 3760*q+1061 := by omega
  rw [xe,ye] at hp
  exact no_585_9 q hp

private theorem no_585_7 (q : Nat) :
    ¬ Reach (672*q+187) (6848*q+1935) := by
  intro hr
  rcases odd_back (672*q+187) (6848*q+1935) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 336*q+92 := by omega
    have ye : y = 7520*q+2122 := by omega
    rw [xe,ye] at hp
    exact no_585_8 q hp
  · omega

private theorem no_585_6 (q : Nat) :
    ¬ Reach (1344*q+377) (5504*q+1558) := by
  intro hr
  rcases odd_back (1344*q+377) (5504*q+1558) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 672*q+187 := by omega
    have ye : y = 6848*q+1935 := by omega
    rw [xe,ye] at hp
    exact no_585_7 q hp
  · have xe : x = 2720*q+760 := by omega
    have ye : y = 2752*q+781 := by omega
    rw [xe,ye] at hp
    exact no_585_11 q hp

private theorem no_585_5 (q : Nat) :
    ¬ Reach (2688*q+757) (2816*q+801) := by
  intro hr
  rcases odd_back (2688*q+757) (2816*q+801) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+377 := by omega
    have ye : y = 5504*q+1558 := by omega
    rw [xe,ye] at hp
    exact no_585_6 q hp
  · omega

private theorem no_585_4 (q : Nat) :
    ¬ Reach (1280*q+360) (5632*q+1602) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+360) (5632*q+1602) (by omega) (by omega) hr
  have xe : x = 2688*q+757 := by omega
  have ye : y = 2816*q+801 := by omega
  rw [xe,ye] at hp
  exact no_585_5 q hp

private theorem no_585_3 (q : Nat) :
    ¬ Reach (2560*q+723) (3072*q+879) := by
  intro hr
  rcases odd_back (2560*q+723) (3072*q+879) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+360 := by omega
    have ye : y = 5632*q+1602 := by omega
    rw [xe,ye] at hp
    exact no_585_4 q hp
  · omega

private theorem no_585_2 (q : Nat) :
    ¬ Reach (512*q+144) (7168*q+2045) := by
  intro hr
  have ha := reach_allowed (512*q+144) (7168*q+2045) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_585_1 (q : Nat) :
    ¬ Reach (1024*q+291) (6144*q+1754) := by
  intro hr
  rcases odd_back (1024*q+291) (6144*q+1754) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+144 := by omega
    have ye : y = 7168*q+2045 := by omega
    rw [xe,ye] at hp
    exact no_585_2 q hp
  · have xe : x = 2560*q+723 := by omega
    have ye : y = 3072*q+879 := by omega
    rw [xe,ye] at hp
    exact no_585_3 q hp

private theorem no_585_0 (q : Nat) :
    ¬ Reach (2048*q+585) (4096*q+1169) := by
  intro hr
  rcases odd_back (2048*q+585) (4096*q+1169) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+291 := by omega
    have ye : y = 6144*q+1754 := by omega
    rw [xe,ye] at hp
    exact no_585_1 q hp
  · omega

theorem blank_halt_not_585_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠585 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+585 := by dsimp [q]; omega
  have hb : b=4096*q+1169 := by omega
  have hr0 : Reach (2048*q+585) (4096*q+1169) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_585_0 q hr0

#print axioms blank_halt_not_585_mod2048

private theorem no_629_11 (q : Nat) :
    ¬ Reach (2560*q+778) (3072*q+945) := by
  intro hr
  have ha := reach_allowed (2560*q+778) (3072*q+945) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_629_10 (q : Nat) :
    ¬ Reach (2592*q+782) (3008*q+921) := by
  intro hr
  have ha := reach_allowed (2592*q+782) (3008*q+921) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_629_9 (q : Nat) :
    ¬ Reach (1092*q+328) (6008*q+1824) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (1092*q+328) (6008*q+1824) hn (by omega) (by omega)
  omega

private theorem no_629_8 (q : Nat) :
    ¬ Reach (2184*q+659) (3824*q+1165) := by
  intro hr
  rcases odd_back (2184*q+659) (3824*q+1165) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1092*q+328 := by omega
    have ye : y = 6008*q+1824 := by omega
    rw [xe,ye] at hp
    exact no_629_9 q hp
  · omega

private theorem no_629_7 (q : Nat) :
    ¬ Reach (272*q+80) (7648*q+2330) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (272*q+80) (7648*q+2330) (by omega) (by omega) hr
  have xe : x = 2184*q+659 := by omega
  have ye : y = 3824*q+1165 := by omega
  rw [xe,ye] at hp
  exact no_629_8 q hp

private theorem no_629_6 (q : Nat) :
    ¬ Reach (544*q+163) (7104*q+2167) := by
  intro hr
  rcases odd_back (544*q+163) (7104*q+2167) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 272*q+80 := by omega
    have ye : y = 7648*q+2330 := by omega
    rw [xe,ye] at hp
    exact no_629_7 q hp
  · omega

private theorem no_629_5 (q : Nat) :
    ¬ Reach (1088*q+329) (6016*q+1838) := by
  intro hr
  rcases odd_back (1088*q+329) (6016*q+1838) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+163 := by omega
    have ye : y = 7104*q+2167 := by omega
    rw [xe,ye] at hp
    exact no_629_6 q hp
  · have xe : x = 2592*q+782 := by omega
    have ye : y = 3008*q+921 := by omega
    rw [xe,ye] at hp
    exact no_629_10 q hp

private theorem no_629_4 (q : Nat) :
    ¬ Reach (2176*q+661) (3840*q+1177) := by
  intro hr
  rcases odd_back (2176*q+661) (3840*q+1177) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+329 := by omega
    have ye : y = 6016*q+1838 := by omega
    rw [xe,ye] at hp
    exact no_629_5 q hp
  · omega

private theorem no_629_3 (q : Nat) :
    ¬ Reach (256*q+76) (7680*q+2354) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+76) (7680*q+2354) (by omega) (by omega) hr
  have xe : x = 2176*q+661 := by omega
  have ye : y = 3840*q+1177 := by omega
  rw [xe,ye] at hp
  exact no_629_4 q hp

private theorem no_629_2 (q : Nat) :
    ¬ Reach (512*q+155) (7168*q+2199) := by
  intro hr
  rcases odd_back (512*q+155) (7168*q+2199) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+76 := by omega
    have ye : y = 7680*q+2354 := by omega
    rw [xe,ye] at hp
    exact no_629_3 q hp
  · omega

private theorem no_629_1 (q : Nat) :
    ¬ Reach (1024*q+313) (6144*q+1886) := by
  intro hr
  rcases odd_back (1024*q+313) (6144*q+1886) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+155 := by omega
    have ye : y = 7168*q+2199 := by omega
    rw [xe,ye] at hp
    exact no_629_2 q hp
  · have xe : x = 2560*q+778 := by omega
    have ye : y = 3072*q+945 := by omega
    rw [xe,ye] at hp
    exact no_629_11 q hp

private theorem no_629_0 (q : Nat) :
    ¬ Reach (2048*q+629) (4096*q+1257) := by
  intro hr
  rcases odd_back (2048*q+629) (4096*q+1257) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+313 := by omega
    have ye : y = 6144*q+1886 := by omega
    rw [xe,ye] at hp
    exact no_629_1 q hp
  · omega

theorem blank_halt_not_629_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠629 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+629 := by dsimp [q]; omega
  have hb : b=4096*q+1257 := by omega
  have hr0 : Reach (2048*q+629) (4096*q+1257) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_629_0 q hr0

#print axioms blank_halt_not_629_mod2048

private theorem no_649_13 (q : Nat) :
    ¬ Reach (2218*q+682) (3756*q+1173) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (2218*q+682) (3756*q+1173) hn (by omega) (by omega)
  omega

private theorem no_649_12 (q : Nat) :
    ¬ Reach (170*q+50) (7852*q+2445) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (170*q+50) (7852*q+2445) hn (by omega) (by omega)
  omega

private theorem no_649_11 (q : Nat) :
    ¬ Reach (340*q+103) (7512*q+2342) := by
  intro hr
  rcases odd_back (340*q+103) (7512*q+2342) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 170*q+50 := by omega
    have ye : y = 7852*q+2445 := by omega
    rw [xe,ye] at hp
    exact no_649_12 q hp
  · have xe : x = 2218*q+682 := by omega
    have ye : y = 3756*q+1173 := by omega
    rw [xe,ye] at hp
    exact no_649_13 q hp

private theorem no_649_10 (q : Nat) :
    ¬ Reach (680*q+209) (6832*q+2133) := by
  intro hr
  rcases odd_back (680*q+209) (6832*q+2133) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 340*q+103 := by omega
    have ye : y = 7512*q+2342 := by omega
    rw [xe,ye] at hp
    exact no_649_11 q hp
  · omega

private theorem no_649_9 (q : Nat) :
    ¬ Reach (1360*q+421) (5472*q+1712) := by
  intro hr
  rcases odd_back (1360*q+421) (5472*q+1712) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 680*q+209 := by omega
    have ye : y = 6832*q+2133 := by omega
    rw [xe,ye] at hp
    exact no_649_10 q hp
  · omega

private theorem no_649_8 (q : Nat) :
    ¬ Reach (2720*q+845) (2752*q+867) := by
  intro hr
  rcases odd_back (2720*q+845) (2752*q+867) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1360*q+421 := by omega
    have ye : y = 5472*q+1712 := by omega
    rw [xe,ye] at hp
    exact no_649_9 q hp
  · omega

private theorem no_649_7 (q : Nat) :
    ¬ Reach (672*q+208) (6848*q+2149) := by
  intro hr
  have ha := reach_allowed (672*q+208) (6848*q+2149) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_649_6 (q : Nat) :
    ¬ Reach (1344*q+419) (5504*q+1730) := by
  intro hr
  rcases odd_back (1344*q+419) (5504*q+1730) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 672*q+208 := by omega
    have ye : y = 6848*q+2149 := by omega
    rw [xe,ye] at hp
    exact no_649_7 q hp
  · have xe : x = 2720*q+845 := by omega
    have ye : y = 2752*q+867 := by omega
    rw [xe,ye] at hp
    exact no_649_8 q hp

private theorem no_649_5 (q : Nat) :
    ¬ Reach (2688*q+841) (2816*q+889) := by
  intro hr
  rcases odd_back (2688*q+841) (2816*q+889) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+419 := by omega
    have ye : y = 5504*q+1730 := by omega
    rw [xe,ye] at hp
    exact no_649_6 q hp
  · omega

private theorem no_649_4 (q : Nat) :
    ¬ Reach (1280*q+400) (5632*q+1778) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+400) (5632*q+1778) (by omega) (by omega) hr
  have xe : x = 2688*q+841 := by omega
  have ye : y = 2816*q+889 := by omega
  rw [xe,ye] at hp
  exact no_649_5 q hp

private theorem no_649_3 (q : Nat) :
    ¬ Reach (2560*q+803) (3072*q+975) := by
  intro hr
  rcases odd_back (2560*q+803) (3072*q+975) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+400 := by omega
    have ye : y = 5632*q+1778 := by omega
    rw [xe,ye] at hp
    exact no_649_4 q hp
  · omega

private theorem no_649_2 (q : Nat) :
    ¬ Reach (512*q+160) (7168*q+2269) := by
  intro hr
  have ha := reach_allowed (512*q+160) (7168*q+2269) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_649_1 (q : Nat) :
    ¬ Reach (1024*q+323) (6144*q+1946) := by
  intro hr
  rcases odd_back (1024*q+323) (6144*q+1946) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+160 := by omega
    have ye : y = 7168*q+2269 := by omega
    rw [xe,ye] at hp
    exact no_649_2 q hp
  · have xe : x = 2560*q+803 := by omega
    have ye : y = 3072*q+975 := by omega
    rw [xe,ye] at hp
    exact no_649_3 q hp

private theorem no_649_0 (q : Nat) :
    ¬ Reach (2048*q+649) (4096*q+1297) := by
  intro hr
  rcases odd_back (2048*q+649) (4096*q+1297) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+323 := by omega
    have ye : y = 6144*q+1946 := by omega
    rw [xe,ye] at hp
    exact no_649_1 q hp
  · omega

theorem blank_halt_not_649_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠649 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+649 := by dsimp [q]; omega
  have hb : b=4096*q+1297 := by omega
  have hr0 : Reach (2048*q+649) (4096*q+1297) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_649_0 q hr0

#print axioms blank_halt_not_649_mod2048

private theorem no_1225_13 (q : Nat) :
    ¬ Reach (2720*q+1610) (2752*q+1641) := by
  intro hr
  have ha := reach_allowed (2720*q+1610) (2752*q+1641) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1225_12 (q : Nat) :
    ¬ Reach (2090*q+1232) (4012*q+2385) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (2090*q+1232) (4012*q+2385) hn (by omega) (by omega)
  omega

private theorem no_1225_11 (q : Nat) :
    ¬ Reach (42*q+22) (8108*q+4813) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (42*q+22) (8108*q+4813) hn (by omega) (by omega)
  omega

private theorem no_1225_10 (q : Nat) :
    ¬ Reach (84*q+47) (8024*q+4766) := by
  intro hr
  rcases odd_back (84*q+47) (8024*q+4766) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 42*q+22 := by omega
    have ye : y = 8108*q+4813 := by omega
    rw [xe,ye] at hp
    exact no_1225_11 q hp
  · have xe : x = 2090*q+1232 := by omega
    have ye : y = 4012*q+2385 := by omega
    rw [xe,ye] at hp
    exact no_1225_12 q hp

private theorem no_1225_9 (q : Nat) :
    ¬ Reach (168*q+97) (7856*q+4669) := by
  intro hr
  rcases odd_back (168*q+97) (7856*q+4669) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 84*q+47 := by omega
    have ye : y = 8024*q+4766 := by omega
    rw [xe,ye] at hp
    exact no_1225_10 q hp
  · omega

private theorem no_1225_8 (q : Nat) :
    ¬ Reach (336*q+197) (7520*q+4472) := by
  intro hr
  rcases odd_back (336*q+197) (7520*q+4472) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 168*q+97 := by omega
    have ye : y = 7856*q+4669 := by omega
    rw [xe,ye] at hp
    exact no_1225_9 q hp
  · omega

private theorem no_1225_7 (q : Nat) :
    ¬ Reach (672*q+397) (6848*q+4075) := by
  intro hr
  rcases odd_back (672*q+397) (6848*q+4075) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 336*q+197 := by omega
    have ye : y = 7520*q+4472 := by omega
    rw [xe,ye] at hp
    exact no_1225_8 q hp
  · omega

private theorem no_1225_6 (q : Nat) :
    ¬ Reach (1344*q+797) (5504*q+3278) := by
  intro hr
  rcases odd_back (1344*q+797) (5504*q+3278) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 672*q+397 := by omega
    have ye : y = 6848*q+4075 := by omega
    rw [xe,ye] at hp
    exact no_1225_7 q hp
  · have xe : x = 2720*q+1610 := by omega
    have ye : y = 2752*q+1641 := by omega
    rw [xe,ye] at hp
    exact no_1225_13 q hp

private theorem no_1225_5 (q : Nat) :
    ¬ Reach (2688*q+1597) (2816*q+1681) := by
  intro hr
  rcases odd_back (2688*q+1597) (2816*q+1681) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+797 := by omega
    have ye : y = 5504*q+3278 := by omega
    rw [xe,ye] at hp
    exact no_1225_6 q hp
  · omega

private theorem no_1225_4 (q : Nat) :
    ¬ Reach (1280*q+760) (5632*q+3362) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+760) (5632*q+3362) (by omega) (by omega) hr
  have xe : x = 2688*q+1597 := by omega
  have ye : y = 2816*q+1681 := by omega
  rw [xe,ye] at hp
  exact no_1225_5 q hp

private theorem no_1225_3 (q : Nat) :
    ¬ Reach (2560*q+1523) (3072*q+1839) := by
  intro hr
  rcases odd_back (2560*q+1523) (3072*q+1839) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+760 := by omega
    have ye : y = 5632*q+3362 := by omega
    rw [xe,ye] at hp
    exact no_1225_4 q hp
  · omega

private theorem no_1225_2 (q : Nat) :
    ¬ Reach (512*q+304) (7168*q+4285) := by
  intro hr
  have ha := reach_allowed (512*q+304) (7168*q+4285) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1225_1 (q : Nat) :
    ¬ Reach (1024*q+611) (6144*q+3674) := by
  intro hr
  rcases odd_back (1024*q+611) (6144*q+3674) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+304 := by omega
    have ye : y = 7168*q+4285 := by omega
    rw [xe,ye] at hp
    exact no_1225_2 q hp
  · have xe : x = 2560*q+1523 := by omega
    have ye : y = 3072*q+1839 := by omega
    rw [xe,ye] at hp
    exact no_1225_3 q hp

private theorem no_1225_0 (q : Nat) :
    ¬ Reach (2048*q+1225) (4096*q+2449) := by
  intro hr
  rcases odd_back (2048*q+1225) (4096*q+2449) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+611 := by omega
    have ye : y = 6144*q+3674 := by omega
    rw [xe,ye] at hp
    exact no_1225_1 q hp
  · omega

theorem blank_halt_not_1225_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1225 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1225 := by dsimp [q]; omega
  have hb : b=4096*q+2449 := by omega
  have hr0 : Reach (2048*q+1225) (4096*q+2449) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1225_0 q hr0

#print axioms blank_halt_not_1225_mod2048

private theorem no_1269_13 (q : Nat) :
    ¬ Reach (2560*q+1578) (3072*q+1905) := by
  intro hr
  have ha := reach_allowed (2560*q+1578) (3072*q+1905) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1269_12 (q : Nat) :
    ¬ Reach (2592*q+1592) (3008*q+1861) := by
  intro hr
  have ha := reach_allowed (2592*q+1592) (3008*q+1861) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1269_11 (q : Nat) :
    ¬ Reach (2082*q+1274) (4028*q+2485) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (2082*q+1274) (4028*q+2485) hn (by omega) (by omega)
  omega

private theorem no_1269_10 (q : Nat) :
    ¬ Reach (34*q+18) (8124*q+5005) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (34*q+18) (8124*q+5005) hn (by omega) (by omega)
  omega

private theorem no_1269_9 (q : Nat) :
    ¬ Reach (68*q+39) (8056*q+4966) := by
  intro hr
  rcases odd_back (68*q+39) (8056*q+4966) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 34*q+18 := by omega
    have ye : y = 8124*q+5005 := by omega
    rw [xe,ye] at hp
    exact no_1269_10 q hp
  · have xe : x = 2082*q+1274 := by omega
    have ye : y = 4028*q+2485 := by omega
    rw [xe,ye] at hp
    exact no_1269_11 q hp

private theorem no_1269_8 (q : Nat) :
    ¬ Reach (136*q+81) (7920*q+4885) := by
  intro hr
  rcases odd_back (136*q+81) (7920*q+4885) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 68*q+39 := by omega
    have ye : y = 8056*q+4966 := by omega
    rw [xe,ye] at hp
    exact no_1269_9 q hp
  · omega

private theorem no_1269_7 (q : Nat) :
    ¬ Reach (272*q+165) (7648*q+4720) := by
  intro hr
  rcases odd_back (272*q+165) (7648*q+4720) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 136*q+81 := by omega
    have ye : y = 7920*q+4885 := by omega
    rw [xe,ye] at hp
    exact no_1269_8 q hp
  · omega

private theorem no_1269_6 (q : Nat) :
    ¬ Reach (544*q+333) (7104*q+4387) := by
  intro hr
  rcases odd_back (544*q+333) (7104*q+4387) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 272*q+165 := by omega
    have ye : y = 7648*q+4720 := by omega
    rw [xe,ye] at hp
    exact no_1269_7 q hp
  · omega

private theorem no_1269_5 (q : Nat) :
    ¬ Reach (1088*q+669) (6016*q+3718) := by
  intro hr
  rcases odd_back (1088*q+669) (6016*q+3718) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+333 := by omega
    have ye : y = 7104*q+4387 := by omega
    rw [xe,ye] at hp
    exact no_1269_6 q hp
  · have xe : x = 2592*q+1592 := by omega
    have ye : y = 3008*q+1861 := by omega
    rw [xe,ye] at hp
    exact no_1269_12 q hp

private theorem no_1269_4 (q : Nat) :
    ¬ Reach (2176*q+1341) (3840*q+2377) := by
  intro hr
  rcases odd_back (2176*q+1341) (3840*q+2377) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+669 := by omega
    have ye : y = 6016*q+3718 := by omega
    rw [xe,ye] at hp
    exact no_1269_5 q hp
  · omega

private theorem no_1269_3 (q : Nat) :
    ¬ Reach (256*q+156) (7680*q+4754) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+156) (7680*q+4754) (by omega) (by omega) hr
  have xe : x = 2176*q+1341 := by omega
  have ye : y = 3840*q+2377 := by omega
  rw [xe,ye] at hp
  exact no_1269_4 q hp

private theorem no_1269_2 (q : Nat) :
    ¬ Reach (512*q+315) (7168*q+4439) := by
  intro hr
  rcases odd_back (512*q+315) (7168*q+4439) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+156 := by omega
    have ye : y = 7680*q+4754 := by omega
    rw [xe,ye] at hp
    exact no_1269_3 q hp
  · omega

private theorem no_1269_1 (q : Nat) :
    ¬ Reach (1024*q+633) (6144*q+3806) := by
  intro hr
  rcases odd_back (1024*q+633) (6144*q+3806) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+315 := by omega
    have ye : y = 7168*q+4439 := by omega
    rw [xe,ye] at hp
    exact no_1269_2 q hp
  · have xe : x = 2560*q+1578 := by omega
    have ye : y = 3072*q+1905 := by omega
    rw [xe,ye] at hp
    exact no_1269_13 q hp

private theorem no_1269_0 (q : Nat) :
    ¬ Reach (2048*q+1269) (4096*q+2537) := by
  intro hr
  rcases odd_back (2048*q+1269) (4096*q+2537) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+633 := by omega
    have ye : y = 6144*q+3806 := by omega
    rw [xe,ye] at hp
    exact no_1269_1 q hp
  · omega

theorem blank_halt_not_1269_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1269 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1269 := by dsimp [q]; omega
  have hb : b=4096*q+2537 := by omega
  have hr0 : Reach (2048*q+1269) (4096*q+2537) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1269_0 q hr0

#print axioms blank_halt_not_1269_mod2048

private theorem no_1461_11 (q : Nat) :
    ¬ Reach (2560*q+1818) (3072*q+2193) := by
  intro hr
  have ha := reach_allowed (2560*q+1818) (3072*q+2193) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1461_10 (q : Nat) :
    ¬ Reach (1348*q+952) (5496*q+3896) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (1348*q+952) (5496*q+3896) hn (by omega) (by omega)
  omega

private theorem no_1461_9 (q : Nat) :
    ¬ Reach (2696*q+1907) (2800*q+1989) := by
  intro hr
  rcases odd_back (2696*q+1907) (2800*q+1989) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1348*q+952 := by omega
    have ye : y = 5496*q+3896 := by omega
    rw [xe,ye] at hp
    exact no_1461_10 q hp
  · omega

private theorem no_1461_8 (q : Nat) :
    ¬ Reach (1296*q+916) (5600*q+3978) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1296*q+916) (5600*q+3978) (by omega) (by omega) hr
  have xe : x = 2696*q+1907 := by omega
  have ye : y = 2800*q+1989 := by omega
  rw [xe,ye] at hp
  exact no_1461_9 q hp

private theorem no_1461_7 (q : Nat) :
    ¬ Reach (2592*q+1835) (3008*q+2143) := by
  intro hr
  rcases odd_back (2592*q+1835) (3008*q+2143) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1296*q+916 := by omega
    have ye : y = 5600*q+3978 := by omega
    rw [xe,ye] at hp
    exact no_1461_8 q hp
  · omega

private theorem no_1461_6 (q : Nat) :
    ¬ Reach (544*q+384) (7104*q+5053) := by
  intro hr
  have ha := reach_allowed (544*q+384) (7104*q+5053) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1461_5 (q : Nat) :
    ¬ Reach (1088*q+771) (6016*q+4282) := by
  intro hr
  rcases odd_back (1088*q+771) (6016*q+4282) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+384 := by omega
    have ye : y = 7104*q+5053 := by omega
    rw [xe,ye] at hp
    exact no_1461_6 q hp
  · have xe : x = 2592*q+1835 := by omega
    have ye : y = 3008*q+2143 := by omega
    rw [xe,ye] at hp
    exact no_1461_7 q hp

private theorem no_1461_4 (q : Nat) :
    ¬ Reach (2176*q+1545) (3840*q+2737) := by
  intro hr
  rcases odd_back (2176*q+1545) (3840*q+2737) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+771 := by omega
    have ye : y = 6016*q+4282 := by omega
    rw [xe,ye] at hp
    exact no_1461_5 q hp
  · omega

private theorem no_1461_3 (q : Nat) :
    ¬ Reach (256*q+180) (7680*q+5474) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+180) (7680*q+5474) (by omega) (by omega) hr
  have xe : x = 2176*q+1545 := by omega
  have ye : y = 3840*q+2737 := by omega
  rw [xe,ye] at hp
  exact no_1461_4 q hp

private theorem no_1461_2 (q : Nat) :
    ¬ Reach (512*q+363) (7168*q+5111) := by
  intro hr
  rcases odd_back (512*q+363) (7168*q+5111) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+180 := by omega
    have ye : y = 7680*q+5474 := by omega
    rw [xe,ye] at hp
    exact no_1461_3 q hp
  · omega

private theorem no_1461_1 (q : Nat) :
    ¬ Reach (1024*q+729) (6144*q+4382) := by
  intro hr
  rcases odd_back (1024*q+729) (6144*q+4382) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+363 := by omega
    have ye : y = 7168*q+5111 := by omega
    rw [xe,ye] at hp
    exact no_1461_2 q hp
  · have xe : x = 2560*q+1818 := by omega
    have ye : y = 3072*q+2193 := by omega
    rw [xe,ye] at hp
    exact no_1461_11 q hp

private theorem no_1461_0 (q : Nat) :
    ¬ Reach (2048*q+1461) (4096*q+2921) := by
  intro hr
  rcases odd_back (2048*q+1461) (4096*q+2921) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+729 := by omega
    have ye : y = 6144*q+4382 := by omega
    rw [xe,ye] at hp
    exact no_1461_1 q hp
  · omega

theorem blank_halt_not_1461_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1461 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1461 := by dsimp [q]; omega
  have hb : b=4096*q+2921 := by omega
  have hr0 : Reach (2048*q+1461) (4096*q+2921) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1461_0 q hr0

#print axioms blank_halt_not_1461_mod2048

private theorem no_1489_13 (q : Nat) :
    ¬ Reach (2698*q+1938) (2796*q+2021) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (2698*q+1938) (2796*q+2021) hn (by omega) (by omega)
  omega

private theorem no_1489_12 (q : Nat) :
    ¬ Reach (650*q+466) (6892*q+4973) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (650*q+466) (6892*q+4973) hn (by omega) (by omega)
  omega

private theorem no_1489_11 (q : Nat) :
    ¬ Reach (1300*q+935) (5592*q+4038) := by
  intro hr
  rcases odd_back (1300*q+935) (5592*q+4038) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 650*q+466 := by omega
    have ye : y = 6892*q+4973 := by omega
    rw [xe,ye] at hp
    exact no_1489_12 q hp
  · have xe : x = 2698*q+1938 := by omega
    have ye : y = 2796*q+2021 := by omega
    rw [xe,ye] at hp
    exact no_1489_13 q hp

private theorem no_1489_10 (q : Nat) :
    ¬ Reach (2600*q+1873) (2992*q+2165) := by
  intro hr
  rcases odd_back (2600*q+1873) (2992*q+2165) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1300*q+935 := by omega
    have ye : y = 5592*q+4038 := by omega
    rw [xe,ye] at hp
    exact no_1489_11 q hp
  · omega

private theorem no_1489_9 (q : Nat) :
    ¬ Reach (1104*q+794) (5984*q+4330) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1104*q+794) (5984*q+4330) (by omega) (by omega) hr
  have xe : x = 2600*q+1873 := by omega
  have ye : y = 2992*q+2165 := by omega
  rw [xe,ye] at hp
  exact no_1489_10 q hp

private theorem no_1489_8 (q : Nat) :
    ¬ Reach (2208*q+1591) (3776*q+2739) := by
  intro hr
  rcases odd_back (2208*q+1591) (3776*q+2739) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1104*q+794 := by omega
    have ye : y = 5984*q+4330 := by omega
    rw [xe,ye] at hp
    exact no_1489_9 q hp
  · omega

private theorem no_1489_7 (q : Nat) :
    ¬ Reach (160*q+113) (7872*q+5703) := by
  intro hr
  have ha := reach_allowed (160*q+113) (7872*q+5703) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1489_6 (q : Nat) :
    ¬ Reach (320*q+229) (7552*q+5474) := by
  intro hr
  rcases odd_back (320*q+229) (7552*q+5474) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 160*q+113 := by omega
    have ye : y = 7872*q+5703 := by omega
    rw [xe,ye] at hp
    exact no_1489_7 q hp
  · have xe : x = 2208*q+1591 := by omega
    have ye : y = 3776*q+2739 := by omega
    rw [xe,ye] at hp
    exact no_1489_8 q hp

private theorem no_1489_5 (q : Nat) :
    ¬ Reach (640*q+461) (6912*q+5013) := by
  intro hr
  rcases odd_back (640*q+461) (6912*q+5013) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 320*q+229 := by omega
    have ye : y = 7552*q+5474 := by omega
    rw [xe,ye] at hp
    exact no_1489_6 q hp
  · omega

private theorem no_1489_4 (q : Nat) :
    ¬ Reach (1280*q+925) (5632*q+4088) := by
  intro hr
  rcases odd_back (1280*q+925) (5632*q+4088) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 640*q+461 := by omega
    have ye : y = 6912*q+5013 := by omega
    rw [xe,ye] at hp
    exact no_1489_5 q hp
  · omega

private theorem no_1489_3 (q : Nat) :
    ¬ Reach (2560*q+1853) (3072*q+2235) := by
  intro hr
  rcases odd_back (2560*q+1853) (3072*q+2235) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+925 := by omega
    have ye : y = 5632*q+4088 := by omega
    rw [xe,ye] at hp
    exact no_1489_4 q hp
  · omega

private theorem no_1489_2 (q : Nat) :
    ¬ Reach (512*q+370) (7168*q+5209) := by
  intro hr
  have ha := reach_allowed (512*q+370) (7168*q+5209) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1489_1 (q : Nat) :
    ¬ Reach (1024*q+743) (6144*q+4466) := by
  intro hr
  rcases odd_back (1024*q+743) (6144*q+4466) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+370 := by omega
    have ye : y = 7168*q+5209 := by omega
    rw [xe,ye] at hp
    exact no_1489_2 q hp
  · have xe : x = 2560*q+1853 := by omega
    have ye : y = 3072*q+2235 := by omega
    rw [xe,ye] at hp
    exact no_1489_3 q hp

private theorem no_1489_0 (q : Nat) :
    ¬ Reach (2048*q+1489) (4096*q+2977) := by
  intro hr
  rcases odd_back (2048*q+1489) (4096*q+2977) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+743 := by omega
    have ye : y = 6144*q+4466 := by omega
    rw [xe,ye] at hp
    exact no_1489_1 q hp
  · omega

theorem blank_halt_not_1489_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1489 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1489 := by dsimp [q]; omega
  have hb : b=4096*q+2977 := by omega
  have hr0 : Reach (2048*q+1489) (4096*q+2977) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1489_0 q hr0

#print axioms blank_halt_not_1489_mod2048

end BB429AutoGroup5

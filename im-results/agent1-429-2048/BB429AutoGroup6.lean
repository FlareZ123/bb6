import BB429RootMod32
import BB429NewResidue
import Lean.Elab.Tactic.Omega

namespace BB429AutoGroup6
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

private theorem no_1589_13 (q : Nat) :
    ¬ Reach (2560*q+1978) (3072*q+2385) := by
  intro hr
  have ha := reach_allowed (2560*q+1978) (3072*q+2385) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1589_12 (q : Nat) :
    ¬ Reach (2210*q+1696) (3772*q+2913) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (2210*q+1696) (3772*q+2913) hn (by omega) (by omega)
  omega

private theorem no_1589_11 (q : Nat) :
    ¬ Reach (162*q+122) (7868*q+6069) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (162*q+122) (7868*q+6069) hn (by omega) (by omega)
  omega

private theorem no_1589_10 (q : Nat) :
    ¬ Reach (324*q+247) (7544*q+5822) := by
  intro hr
  rcases odd_back (324*q+247) (7544*q+5822) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 162*q+122 := by omega
    have ye : y = 7868*q+6069 := by omega
    rw [xe,ye] at hp
    exact no_1589_11 q hp
  · have xe : x = 2210*q+1696 := by omega
    have ye : y = 3772*q+2913 := by omega
    rw [xe,ye] at hp
    exact no_1589_12 q hp

private theorem no_1589_9 (q : Nat) :
    ¬ Reach (648*q+497) (6896*q+5325) := by
  intro hr
  rcases odd_back (648*q+497) (6896*q+5325) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 324*q+247 := by omega
    have ye : y = 7544*q+5822 := by omega
    rw [xe,ye] at hp
    exact no_1589_10 q hp
  · omega

private theorem no_1589_8 (q : Nat) :
    ¬ Reach (1296*q+997) (5600*q+4328) := by
  intro hr
  rcases odd_back (1296*q+997) (5600*q+4328) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 648*q+497 := by omega
    have ye : y = 6896*q+5325 := by omega
    rw [xe,ye] at hp
    exact no_1589_9 q hp
  · omega

private theorem no_1589_7 (q : Nat) :
    ¬ Reach (2592*q+1997) (3008*q+2331) := by
  intro hr
  rcases odd_back (2592*q+1997) (3008*q+2331) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1296*q+997 := by omega
    have ye : y = 5600*q+4328 := by omega
    rw [xe,ye] at hp
    exact no_1589_8 q hp
  · omega

private theorem no_1589_6 (q : Nat) :
    ¬ Reach (544*q+418) (7104*q+5497) := by
  intro hr
  have ha := reach_allowed (544*q+418) (7104*q+5497) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1589_5 (q : Nat) :
    ¬ Reach (1088*q+839) (6016*q+4658) := by
  intro hr
  rcases odd_back (1088*q+839) (6016*q+4658) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+418 := by omega
    have ye : y = 7104*q+5497 := by omega
    rw [xe,ye] at hp
    exact no_1589_6 q hp
  · have xe : x = 2592*q+1997 := by omega
    have ye : y = 3008*q+2331 := by omega
    rw [xe,ye] at hp
    exact no_1589_7 q hp

private theorem no_1589_4 (q : Nat) :
    ¬ Reach (2176*q+1681) (3840*q+2977) := by
  intro hr
  rcases odd_back (2176*q+1681) (3840*q+2977) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+839 := by omega
    have ye : y = 6016*q+4658 := by omega
    rw [xe,ye] at hp
    exact no_1589_5 q hp
  · omega

private theorem no_1589_3 (q : Nat) :
    ¬ Reach (256*q+196) (7680*q+5954) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+196) (7680*q+5954) (by omega) (by omega) hr
  have xe : x = 2176*q+1681 := by omega
  have ye : y = 3840*q+2977 := by omega
  rw [xe,ye] at hp
  exact no_1589_4 q hp

private theorem no_1589_2 (q : Nat) :
    ¬ Reach (512*q+395) (7168*q+5559) := by
  intro hr
  rcases odd_back (512*q+395) (7168*q+5559) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+196 := by omega
    have ye : y = 7680*q+5954 := by omega
    rw [xe,ye] at hp
    exact no_1589_3 q hp
  · omega

private theorem no_1589_1 (q : Nat) :
    ¬ Reach (1024*q+793) (6144*q+4766) := by
  intro hr
  rcases odd_back (1024*q+793) (6144*q+4766) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+395 := by omega
    have ye : y = 7168*q+5559 := by omega
    rw [xe,ye] at hp
    exact no_1589_2 q hp
  · have xe : x = 2560*q+1978 := by omega
    have ye : y = 3072*q+2385 := by omega
    rw [xe,ye] at hp
    exact no_1589_13 q hp

private theorem no_1589_0 (q : Nat) :
    ¬ Reach (2048*q+1589) (4096*q+3177) := by
  intro hr
  rcases odd_back (2048*q+1589) (4096*q+3177) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+793 := by omega
    have ye : y = 6144*q+4766 := by omega
    rw [xe,ye] at hp
    exact no_1589_1 q hp
  · omega

theorem blank_halt_not_1589_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1589 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1589 := by dsimp [q]; omega
  have hb : b=4096*q+3177 := by omega
  have hr0 : Reach (2048*q+1589) (4096*q+3177) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1589_0 q hr0

#print axioms blank_halt_not_1589_mod2048

private theorem no_1717_8 (q : Nat) :
    ¬ Reach (2560*q+2138) (3072*q+2577) := by
  intro hr
  have ha := reach_allowed (2560*q+2138) (3072*q+2577) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1717_7 (q : Nat) :
    ¬ Reach (2592*q+2159) (3008*q+2519) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_7_7 n (2592*q+2159) (3008*q+2519) hn (by omega)
  omega

private theorem no_1717_6 (q : Nat) :
    ¬ Reach (544*q+452) (7104*q+5941) := by
  intro hr
  have ha := reach_allowed (544*q+452) (7104*q+5941) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1717_5 (q : Nat) :
    ¬ Reach (1088*q+907) (6016*q+5034) := by
  intro hr
  rcases odd_back (1088*q+907) (6016*q+5034) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+452 := by omega
    have ye : y = 7104*q+5941 := by omega
    rw [xe,ye] at hp
    exact no_1717_6 q hp
  · have xe : x = 2592*q+2159 := by omega
    have ye : y = 3008*q+2519 := by omega
    rw [xe,ye] at hp
    exact no_1717_7 q hp

private theorem no_1717_4 (q : Nat) :
    ¬ Reach (2176*q+1817) (3840*q+3217) := by
  intro hr
  rcases odd_back (2176*q+1817) (3840*q+3217) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+907 := by omega
    have ye : y = 6016*q+5034 := by omega
    rw [xe,ye] at hp
    exact no_1717_5 q hp
  · omega

private theorem no_1717_3 (q : Nat) :
    ¬ Reach (256*q+212) (7680*q+6434) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+212) (7680*q+6434) (by omega) (by omega) hr
  have xe : x = 2176*q+1817 := by omega
  have ye : y = 3840*q+3217 := by omega
  rw [xe,ye] at hp
  exact no_1717_4 q hp

private theorem no_1717_2 (q : Nat) :
    ¬ Reach (512*q+427) (7168*q+6007) := by
  intro hr
  rcases odd_back (512*q+427) (7168*q+6007) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+212 := by omega
    have ye : y = 7680*q+6434 := by omega
    rw [xe,ye] at hp
    exact no_1717_3 q hp
  · omega

private theorem no_1717_1 (q : Nat) :
    ¬ Reach (1024*q+857) (6144*q+5150) := by
  intro hr
  rcases odd_back (1024*q+857) (6144*q+5150) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+427 := by omega
    have ye : y = 7168*q+6007 := by omega
    rw [xe,ye] at hp
    exact no_1717_2 q hp
  · have xe : x = 2560*q+2138 := by omega
    have ye : y = 3072*q+2577 := by omega
    rw [xe,ye] at hp
    exact no_1717_8 q hp

private theorem no_1717_0 (q : Nat) :
    ¬ Reach (2048*q+1717) (4096*q+3433) := by
  intro hr
  rcases odd_back (2048*q+1717) (4096*q+3433) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+857 := by omega
    have ye : y = 6144*q+5150 := by omega
    rw [xe,ye] at hp
    exact no_1717_1 q hp
  · omega

theorem blank_halt_not_1717_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1717 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1717 := by dsimp [q]; omega
  have hb : b=4096*q+3433 := by omega
  have hr0 : Reach (2048*q+1717) (4096*q+3433) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1717_0 q hr0

#print axioms blank_halt_not_1717_mod2048

private theorem no_1737_11 (q : Nat) :
    ¬ Reach (2720*q+2290) (2752*q+2329) := by
  intro hr
  have ha := reach_allowed (2720*q+2290) (2752*q+2329) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1737_10 (q : Nat) :
    ¬ Reach (84*q+68) (8024*q+6772) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (84*q+68) (8024*q+6772) hn (by omega) (by omega)
  omega

private theorem no_1737_9 (q : Nat) :
    ¬ Reach (168*q+139) (7856*q+6633) := by
  intro hr
  rcases odd_back (168*q+139) (7856*q+6633) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 84*q+68 := by omega
    have ye : y = 8024*q+6772 := by omega
    rw [xe,ye] at hp
    exact no_1737_10 q hp
  · omega

private theorem no_1737_8 (q : Nat) :
    ¬ Reach (336*q+281) (7520*q+6352) := by
  intro hr
  rcases odd_back (336*q+281) (7520*q+6352) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 168*q+139 := by omega
    have ye : y = 7856*q+6633 := by omega
    rw [xe,ye] at hp
    exact no_1737_9 q hp
  · omega

private theorem no_1737_7 (q : Nat) :
    ¬ Reach (672*q+565) (6848*q+5787) := by
  intro hr
  rcases odd_back (672*q+565) (6848*q+5787) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 336*q+281 := by omega
    have ye : y = 7520*q+6352 := by omega
    rw [xe,ye] at hp
    exact no_1737_8 q hp
  · omega

private theorem no_1737_6 (q : Nat) :
    ¬ Reach (1344*q+1133) (5504*q+4654) := by
  intro hr
  rcases odd_back (1344*q+1133) (5504*q+4654) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 672*q+565 := by omega
    have ye : y = 6848*q+5787 := by omega
    rw [xe,ye] at hp
    exact no_1737_7 q hp
  · have xe : x = 2720*q+2290 := by omega
    have ye : y = 2752*q+2329 := by omega
    rw [xe,ye] at hp
    exact no_1737_11 q hp

private theorem no_1737_5 (q : Nat) :
    ¬ Reach (2688*q+2269) (2816*q+2385) := by
  intro hr
  rcases odd_back (2688*q+2269) (2816*q+2385) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+1133 := by omega
    have ye : y = 5504*q+4654 := by omega
    rw [xe,ye] at hp
    exact no_1737_6 q hp
  · omega

private theorem no_1737_4 (q : Nat) :
    ¬ Reach (1280*q+1080) (5632*q+4770) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+1080) (5632*q+4770) (by omega) (by omega) hr
  have xe : x = 2688*q+2269 := by omega
  have ye : y = 2816*q+2385 := by omega
  rw [xe,ye] at hp
  exact no_1737_5 q hp

private theorem no_1737_3 (q : Nat) :
    ¬ Reach (2560*q+2163) (3072*q+2607) := by
  intro hr
  rcases odd_back (2560*q+2163) (3072*q+2607) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+1080 := by omega
    have ye : y = 5632*q+4770 := by omega
    rw [xe,ye] at hp
    exact no_1737_4 q hp
  · omega

private theorem no_1737_2 (q : Nat) :
    ¬ Reach (512*q+432) (7168*q+6077) := by
  intro hr
  have ha := reach_allowed (512*q+432) (7168*q+6077) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1737_1 (q : Nat) :
    ¬ Reach (1024*q+867) (6144*q+5210) := by
  intro hr
  rcases odd_back (1024*q+867) (6144*q+5210) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+432 := by omega
    have ye : y = 7168*q+6077 := by omega
    rw [xe,ye] at hp
    exact no_1737_2 q hp
  · have xe : x = 2560*q+2163 := by omega
    have ye : y = 3072*q+2607 := by omega
    rw [xe,ye] at hp
    exact no_1737_3 q hp

private theorem no_1737_0 (q : Nat) :
    ¬ Reach (2048*q+1737) (4096*q+3473) := by
  intro hr
  rcases odd_back (2048*q+1737) (4096*q+3473) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+867 := by omega
    have ye : y = 6144*q+5210 := by omega
    rw [xe,ye] at hp
    exact no_1737_1 q hp
  · omega

theorem blank_halt_not_1737_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1737 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1737 := by dsimp [q]; omega
  have hb : b=4096*q+3473 := by omega
  have hr0 : Reach (2048*q+1737) (4096*q+3473) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1737_0 q hr0

#print axioms blank_halt_not_1737_mod2048

private theorem no_1781_11 (q : Nat) :
    ¬ Reach (2560*q+2218) (3072*q+2673) := by
  intro hr
  have ha := reach_allowed (2560*q+2218) (3072*q+2673) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1781_10 (q : Nat) :
    ¬ Reach (2592*q+2240) (3008*q+2613) := by
  intro hr
  have ha := reach_allowed (2592*q+2240) (3008*q+2613) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1781_9 (q : Nat) :
    ¬ Reach (68*q+56) (8056*q+6980) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (68*q+56) (8056*q+6980) hn (by omega) (by omega)
  omega

private theorem no_1781_8 (q : Nat) :
    ¬ Reach (136*q+115) (7920*q+6865) := by
  intro hr
  rcases odd_back (136*q+115) (7920*q+6865) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 68*q+56 := by omega
    have ye : y = 8056*q+6980 := by omega
    rw [xe,ye] at hp
    exact no_1781_9 q hp
  · omega

private theorem no_1781_7 (q : Nat) :
    ¬ Reach (272*q+233) (7648*q+6632) := by
  intro hr
  rcases odd_back (272*q+233) (7648*q+6632) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 136*q+115 := by omega
    have ye : y = 7920*q+6865 := by omega
    rw [xe,ye] at hp
    exact no_1781_8 q hp
  · omega

private theorem no_1781_6 (q : Nat) :
    ¬ Reach (544*q+469) (7104*q+6163) := by
  intro hr
  rcases odd_back (544*q+469) (7104*q+6163) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 272*q+233 := by omega
    have ye : y = 7648*q+6632 := by omega
    rw [xe,ye] at hp
    exact no_1781_7 q hp
  · omega

private theorem no_1781_5 (q : Nat) :
    ¬ Reach (1088*q+941) (6016*q+5222) := by
  intro hr
  rcases odd_back (1088*q+941) (6016*q+5222) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+469 := by omega
    have ye : y = 7104*q+6163 := by omega
    rw [xe,ye] at hp
    exact no_1781_6 q hp
  · have xe : x = 2592*q+2240 := by omega
    have ye : y = 3008*q+2613 := by omega
    rw [xe,ye] at hp
    exact no_1781_10 q hp

private theorem no_1781_4 (q : Nat) :
    ¬ Reach (2176*q+1885) (3840*q+3337) := by
  intro hr
  rcases odd_back (2176*q+1885) (3840*q+3337) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+941 := by omega
    have ye : y = 6016*q+5222 := by omega
    rw [xe,ye] at hp
    exact no_1781_5 q hp
  · omega

private theorem no_1781_3 (q : Nat) :
    ¬ Reach (256*q+220) (7680*q+6674) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+220) (7680*q+6674) (by omega) (by omega) hr
  have xe : x = 2176*q+1885 := by omega
  have ye : y = 3840*q+3337 := by omega
  rw [xe,ye] at hp
  exact no_1781_4 q hp

private theorem no_1781_2 (q : Nat) :
    ¬ Reach (512*q+443) (7168*q+6231) := by
  intro hr
  rcases odd_back (512*q+443) (7168*q+6231) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+220 := by omega
    have ye : y = 7680*q+6674 := by omega
    rw [xe,ye] at hp
    exact no_1781_3 q hp
  · omega

private theorem no_1781_1 (q : Nat) :
    ¬ Reach (1024*q+889) (6144*q+5342) := by
  intro hr
  rcases odd_back (1024*q+889) (6144*q+5342) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+443 := by omega
    have ye : y = 7168*q+6231 := by omega
    rw [xe,ye] at hp
    exact no_1781_2 q hp
  · have xe : x = 2560*q+2218 := by omega
    have ye : y = 3072*q+2673 := by omega
    rw [xe,ye] at hp
    exact no_1781_11 q hp

private theorem no_1781_0 (q : Nat) :
    ¬ Reach (2048*q+1781) (4096*q+3561) := by
  intro hr
  rcases odd_back (2048*q+1781) (4096*q+3561) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+889 := by omega
    have ye : y = 6144*q+5342 := by omega
    rw [xe,ye] at hp
    exact no_1781_1 q hp
  · omega

theorem blank_halt_not_1781_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1781 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1781 := by dsimp [q]; omega
  have hb : b=4096*q+3561 := by omega
  have hr0 : Reach (2048*q+1781) (4096*q+3561) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1781_0 q hr0

#print axioms blank_halt_not_1781_mod2048

private theorem no_1873_16 (q : Nat) :
    ¬ Reach (276*q+248) (7640*q+6952) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (276*q+248) (7640*q+6952) hn (by omega) (by omega)
  omega

private theorem no_1873_15 (q : Nat) :
    ¬ Reach (552*q+499) (7088*q+6453) := by
  intro hr
  rcases odd_back (552*q+499) (7088*q+6453) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 276*q+248 := by omega
    have ye : y = 7640*q+6952 := by omega
    rw [xe,ye] at hp
    exact no_1873_16 q hp
  · omega

private theorem no_1873_14 (q : Nat) :
    ¬ Reach (1104*q+1001) (5984*q+5452) := by
  intro hr
  rcases odd_back (1104*q+1001) (5984*q+5452) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 552*q+499 := by omega
    have ye : y = 7088*q+6453 := by omega
    rw [xe,ye] at hp
    exact no_1873_15 q hp
  · omega

private theorem no_1873_13 (q : Nat) :
    ¬ Reach (2208*q+2005) (3776*q+3447) := by
  intro hr
  rcases odd_back (2208*q+2005) (3776*q+3447) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1104*q+1001 := by omega
    have ye : y = 5984*q+5452 := by omega
    rw [xe,ye] at hp
    exact no_1873_14 q hp
  · omega

private theorem no_1873_12 (q : Nat) :
    ¬ Reach (2570*q+2330) (3052*q+2781) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (2570*q+2330) (3052*q+2781) hn (by omega) (by omega)
  omega

private theorem no_1873_11 (q : Nat) :
    ¬ Reach (522*q+472) (7148*q+6505) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (522*q+472) (7148*q+6505) hn (by omega) (by omega)
  omega

private theorem no_1873_10 (q : Nat) :
    ¬ Reach (1044*q+947) (6104*q+5558) := by
  intro hr
  rcases odd_back (1044*q+947) (6104*q+5558) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 522*q+472 := by omega
    have ye : y = 7148*q+6505 := by omega
    rw [xe,ye] at hp
    exact no_1873_11 q hp
  · have xe : x = 2570*q+2330 := by omega
    have ye : y = 3052*q+2781 := by omega
    rw [xe,ye] at hp
    exact no_1873_12 q hp

private theorem no_1873_9 (q : Nat) :
    ¬ Reach (2088*q+1897) (4016*q+3661) := by
  intro hr
  rcases odd_back (2088*q+1897) (4016*q+3661) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1044*q+947 := by omega
    have ye : y = 6104*q+5558 := by omega
    rw [xe,ye] at hp
    exact no_1873_10 q hp
  · omega

private theorem no_1873_8 (q : Nat) :
    ¬ Reach (80*q+70) (8032*q+7322) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (80*q+70) (8032*q+7322) (by omega) (by omega) hr
  have xe : x = 2088*q+1897 := by omega
  have ye : y = 4016*q+3661 := by omega
  rw [xe,ye] at hp
  exact no_1873_9 q hp

private theorem no_1873_7 (q : Nat) :
    ¬ Reach (160*q+143) (7872*q+7179) := by
  intro hr
  rcases odd_back (160*q+143) (7872*q+7179) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 80*q+70 := by omega
    have ye : y = 8032*q+7322 := by omega
    rw [xe,ye] at hp
    exact no_1873_8 q hp
  · omega

private theorem no_1873_6 (q : Nat) :
    ¬ Reach (320*q+289) (7552*q+6890) := by
  intro hr
  rcases odd_back (320*q+289) (7552*q+6890) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 160*q+143 := by omega
    have ye : y = 7872*q+7179 := by omega
    rw [xe,ye] at hp
    exact no_1873_7 q hp
  · have xe : x = 2208*q+2005 := by omega
    have ye : y = 3776*q+3447 := by omega
    rw [xe,ye] at hp
    exact no_1873_13 q hp

private theorem no_1873_5 (q : Nat) :
    ¬ Reach (640*q+581) (6912*q+6309) := by
  intro hr
  rcases odd_back (640*q+581) (6912*q+6309) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 320*q+289 := by omega
    have ye : y = 7552*q+6890 := by omega
    rw [xe,ye] at hp
    exact no_1873_6 q hp
  · omega

private theorem no_1873_4 (q : Nat) :
    ¬ Reach (1280*q+1165) (5632*q+5144) := by
  intro hr
  rcases odd_back (1280*q+1165) (5632*q+5144) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 640*q+581 := by omega
    have ye : y = 6912*q+6309 := by omega
    rw [xe,ye] at hp
    exact no_1873_5 q hp
  · omega

private theorem no_1873_3 (q : Nat) :
    ¬ Reach (2560*q+2333) (3072*q+2811) := by
  intro hr
  rcases odd_back (2560*q+2333) (3072*q+2811) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+1165 := by omega
    have ye : y = 5632*q+5144 := by omega
    rw [xe,ye] at hp
    exact no_1873_4 q hp
  · omega

private theorem no_1873_2 (q : Nat) :
    ¬ Reach (512*q+466) (7168*q+6553) := by
  intro hr
  have ha := reach_allowed (512*q+466) (7168*q+6553) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1873_1 (q : Nat) :
    ¬ Reach (1024*q+935) (6144*q+5618) := by
  intro hr
  rcases odd_back (1024*q+935) (6144*q+5618) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+466 := by omega
    have ye : y = 7168*q+6553 := by omega
    rw [xe,ye] at hp
    exact no_1873_2 q hp
  · have xe : x = 2560*q+2333 := by omega
    have ye : y = 3072*q+2811 := by omega
    rw [xe,ye] at hp
    exact no_1873_3 q hp

private theorem no_1873_0 (q : Nat) :
    ¬ Reach (2048*q+1873) (4096*q+3745) := by
  intro hr
  rcases odd_back (2048*q+1873) (4096*q+3745) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+935 := by omega
    have ye : y = 6144*q+5618 := by omega
    rw [xe,ye] at hp
    exact no_1873_1 q hp
  · omega

theorem blank_halt_not_1873_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1873 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1873 := by dsimp [q]; omega
  have hb : b=4096*q+3745 := by omega
  have hr0 : Reach (2048*q+1873) (4096*q+3745) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1873_0 q hr0

#print axioms blank_halt_not_1873_mod2048

private theorem no_2001_11 (q : Nat) :
    ¬ Reach (1300*q+1260) (5592*q+5436) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (1300*q+1260) (5592*q+5436) hn (by omega) (by omega)
  omega

private theorem no_2001_10 (q : Nat) :
    ¬ Reach (2600*q+2523) (2992*q+2913) := by
  intro hr
  rcases odd_back (2600*q+2523) (2992*q+2913) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1300*q+1260 := by omega
    have ye : y = 5592*q+5436 := by omega
    rw [xe,ye] at hp
    exact no_2001_11 q hp
  · omega

private theorem no_2001_9 (q : Nat) :
    ¬ Reach (1104*q+1070) (5984*q+5826) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1104*q+1070) (5984*q+5826) (by omega) (by omega) hr
  have xe : x = 2600*q+2523 := by omega
  have ye : y = 2992*q+2913 := by omega
  rw [xe,ye] at hp
  exact no_2001_10 q hp

private theorem no_2001_8 (q : Nat) :
    ¬ Reach (2208*q+2143) (3776*q+3683) := by
  intro hr
  rcases odd_back (2208*q+2143) (3776*q+3683) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1104*q+1070 := by omega
    have ye : y = 5984*q+5826 := by omega
    rw [xe,ye] at hp
    exact no_2001_9 q hp
  · omega

private theorem no_2001_7 (q : Nat) :
    ¬ Reach (160*q+153) (7872*q+7671) := by
  intro hr
  have ha := reach_allowed (160*q+153) (7872*q+7671) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_2001_6 (q : Nat) :
    ¬ Reach (320*q+309) (7552*q+7362) := by
  intro hr
  rcases odd_back (320*q+309) (7552*q+7362) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 160*q+153 := by omega
    have ye : y = 7872*q+7671 := by omega
    rw [xe,ye] at hp
    exact no_2001_7 q hp
  · have xe : x = 2208*q+2143 := by omega
    have ye : y = 3776*q+3683 := by omega
    rw [xe,ye] at hp
    exact no_2001_8 q hp

private theorem no_2001_5 (q : Nat) :
    ¬ Reach (640*q+621) (6912*q+6741) := by
  intro hr
  rcases odd_back (640*q+621) (6912*q+6741) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 320*q+309 := by omega
    have ye : y = 7552*q+7362 := by omega
    rw [xe,ye] at hp
    exact no_2001_6 q hp
  · omega

private theorem no_2001_4 (q : Nat) :
    ¬ Reach (1280*q+1245) (5632*q+5496) := by
  intro hr
  rcases odd_back (1280*q+1245) (5632*q+5496) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 640*q+621 := by omega
    have ye : y = 6912*q+6741 := by omega
    rw [xe,ye] at hp
    exact no_2001_5 q hp
  · omega

private theorem no_2001_3 (q : Nat) :
    ¬ Reach (2560*q+2493) (3072*q+3003) := by
  intro hr
  rcases odd_back (2560*q+2493) (3072*q+3003) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+1245 := by omega
    have ye : y = 5632*q+5496 := by omega
    rw [xe,ye] at hp
    exact no_2001_4 q hp
  · omega

private theorem no_2001_2 (q : Nat) :
    ¬ Reach (512*q+498) (7168*q+7001) := by
  intro hr
  have ha := reach_allowed (512*q+498) (7168*q+7001) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_2001_1 (q : Nat) :
    ¬ Reach (1024*q+999) (6144*q+6002) := by
  intro hr
  rcases odd_back (1024*q+999) (6144*q+6002) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+498 := by omega
    have ye : y = 7168*q+7001 := by omega
    rw [xe,ye] at hp
    exact no_2001_2 q hp
  · have xe : x = 2560*q+2493 := by omega
    have ye : y = 3072*q+3003 := by omega
    rw [xe,ye] at hp
    exact no_2001_3 q hp

private theorem no_2001_0 (q : Nat) :
    ¬ Reach (2048*q+2001) (4096*q+4001) := by
  intro hr
  rcases odd_back (2048*q+2001) (4096*q+4001) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+999 := by omega
    have ye : y = 6144*q+6002 := by omega
    rw [xe,ye] at hp
    exact no_2001_1 q hp
  · omega

theorem blank_halt_not_2001_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠2001 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+2001 := by dsimp [q]; omega
  have hb : b=4096*q+4001 := by omega
  have hr0 : Reach (2048*q+2001) (4096*q+4001) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_2001_0 q hr0

#print axioms blank_halt_not_2001_mod2048

end BB429AutoGroup6

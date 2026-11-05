import BB429RootMod32
import BB429NewResidue
import Lean.Elab.Tactic.Omega

namespace BB429AutoGroup4
open BB429NewResidue

set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Exact inverse-tree certificate for the all-natural 1617 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1617_9 (q : Nat) :
    ¬ Reach (2208*q+1729) (3776*q+2975) := by
  intro hr
  have ha := reach_allowed (2208*q+1729) (3776*q+2975) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1617_8 (q : Nat) :
    ¬ Reach (80*q+60) (8032*q+6318) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (80*q+60) (8032*q+6318) hn (by omega) (by omega)
  omega

private theorem no_1617_7 (q : Nat) :
    ¬ Reach (160*q+123) (7872*q+6195) := by
  intro hr
  rcases odd_back (160*q+123) (7872*q+6195) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 80*q+60 := by omega
    have ye : y = 8032*q+6318 := by omega
    rw [xe,ye] at hp
    exact no_1617_8 q hp
  · omega

private theorem no_1617_6 (q : Nat) :
    ¬ Reach (320*q+249) (7552*q+5946) := by
  intro hr
  rcases odd_back (320*q+249) (7552*q+5946) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 160*q+123 := by omega
    have ye : y = 7872*q+6195 := by omega
    rw [xe,ye] at hp
    exact no_1617_7 q hp
  · have xe : x = 2208*q+1729 := by omega
    have ye : y = 3776*q+2975 := by omega
    rw [xe,ye] at hp
    exact no_1617_9 q hp

private theorem no_1617_5 (q : Nat) :
    ¬ Reach (640*q+501) (6912*q+5445) := by
  intro hr
  rcases odd_back (640*q+501) (6912*q+5445) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 320*q+249 := by omega
    have ye : y = 7552*q+5946 := by omega
    rw [xe,ye] at hp
    exact no_1617_6 q hp
  · omega

private theorem no_1617_4 (q : Nat) :
    ¬ Reach (1280*q+1005) (5632*q+4440) := by
  intro hr
  rcases odd_back (1280*q+1005) (5632*q+4440) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 640*q+501 := by omega
    have ye : y = 6912*q+5445 := by omega
    rw [xe,ye] at hp
    exact no_1617_5 q hp
  · omega

private theorem no_1617_3 (q : Nat) :
    ¬ Reach (2560*q+2013) (3072*q+2427) := by
  intro hr
  rcases odd_back (2560*q+2013) (3072*q+2427) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+1005 := by omega
    have ye : y = 5632*q+4440 := by omega
    rw [xe,ye] at hp
    exact no_1617_4 q hp
  · omega

private theorem no_1617_2 (q : Nat) :
    ¬ Reach (512*q+402) (7168*q+5657) := by
  intro hr
  have ha := reach_allowed (512*q+402) (7168*q+5657) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1617_1 (q : Nat) :
    ¬ Reach (1024*q+807) (6144*q+4850) := by
  intro hr
  rcases odd_back (1024*q+807) (6144*q+4850) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+402 := by omega
    have ye : y = 7168*q+5657 := by omega
    rw [xe,ye] at hp
    exact no_1617_2 q hp
  · have xe : x = 2560*q+2013 := by omega
    have ye : y = 3072*q+2427 := by omega
    rw [xe,ye] at hp
    exact no_1617_3 q hp

private theorem no_1617_0 (q : Nat) :
    ¬ Reach (2048*q+1617) (4096*q+3233) := by
  intro hr
  rcases odd_back (2048*q+1617) (4096*q+3233) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+807 := by omega
    have ye : y = 6144*q+4850 := by omega
    rw [xe,ye] at hp
    exact no_1617_1 q hp
  · omega

theorem blank_halt_not_1617_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1617 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1617 := by dsimp [q]; omega
  have hb : b=4096*q+3233 := by omega
  have hr0 : Reach (2048*q+1617) (4096*q+3233) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1617_0 q hr0

#print axioms blank_halt_not_1617_mod2048

/-- Exact inverse-tree certificate for the all-natural 1653 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1653_10 (q : Nat) :
    ¬ Reach (2560*q+2058) (3072*q+2481) := by
  intro hr
  have ha := reach_allowed (2560*q+2058) (3072*q+2481) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1653_9 (q : Nat) :
    ¬ Reach (2592*q+2078) (3008*q+2425) := by
  intro hr
  have ha := reach_allowed (2592*q+2078) (3008*q+2425) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1653_8 (q : Nat) :
    ¬ Reach (2184*q+1751) (3824*q+3077) := by
  intro hr
  have ha := reach_allowed (2184*q+1751) (3824*q+3077) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1653_7 (q : Nat) :
    ¬ Reach (272*q+216) (7648*q+6154) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (272*q+216) (7648*q+6154) (by omega) (by omega) hr
  have xe : x = 2184*q+1751 := by omega
  have ye : y = 3824*q+3077 := by omega
  rw [xe,ye] at hp
  exact no_1653_8 q hp

private theorem no_1653_6 (q : Nat) :
    ¬ Reach (544*q+435) (7104*q+5719) := by
  intro hr
  rcases odd_back (544*q+435) (7104*q+5719) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 272*q+216 := by omega
    have ye : y = 7648*q+6154 := by omega
    rw [xe,ye] at hp
    exact no_1653_7 q hp
  · omega

private theorem no_1653_5 (q : Nat) :
    ¬ Reach (1088*q+873) (6016*q+4846) := by
  intro hr
  rcases odd_back (1088*q+873) (6016*q+4846) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+435 := by omega
    have ye : y = 7104*q+5719 := by omega
    rw [xe,ye] at hp
    exact no_1653_6 q hp
  · have xe : x = 2592*q+2078 := by omega
    have ye : y = 3008*q+2425 := by omega
    rw [xe,ye] at hp
    exact no_1653_9 q hp

private theorem no_1653_4 (q : Nat) :
    ¬ Reach (2176*q+1749) (3840*q+3097) := by
  intro hr
  rcases odd_back (2176*q+1749) (3840*q+3097) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+873 := by omega
    have ye : y = 6016*q+4846 := by omega
    rw [xe,ye] at hp
    exact no_1653_5 q hp
  · omega

private theorem no_1653_3 (q : Nat) :
    ¬ Reach (256*q+204) (7680*q+6194) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+204) (7680*q+6194) (by omega) (by omega) hr
  have xe : x = 2176*q+1749 := by omega
  have ye : y = 3840*q+3097 := by omega
  rw [xe,ye] at hp
  exact no_1653_4 q hp

private theorem no_1653_2 (q : Nat) :
    ¬ Reach (512*q+411) (7168*q+5783) := by
  intro hr
  rcases odd_back (512*q+411) (7168*q+5783) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+204 := by omega
    have ye : y = 7680*q+6194 := by omega
    rw [xe,ye] at hp
    exact no_1653_3 q hp
  · omega

private theorem no_1653_1 (q : Nat) :
    ¬ Reach (1024*q+825) (6144*q+4958) := by
  intro hr
  rcases odd_back (1024*q+825) (6144*q+4958) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+411 := by omega
    have ye : y = 7168*q+5783 := by omega
    rw [xe,ye] at hp
    exact no_1653_2 q hp
  · have xe : x = 2560*q+2058 := by omega
    have ye : y = 3072*q+2481 := by omega
    rw [xe,ye] at hp
    exact no_1653_10 q hp

private theorem no_1653_0 (q : Nat) :
    ¬ Reach (2048*q+1653) (4096*q+3305) := by
  intro hr
  rcases odd_back (2048*q+1653) (4096*q+3305) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+825 := by omega
    have ye : y = 6144*q+4958 := by omega
    rw [xe,ye] at hp
    exact no_1653_1 q hp
  · omega

theorem blank_halt_not_1653_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1653 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1653 := by dsimp [q]; omega
  have hb : b=4096*q+3305 := by omega
  have hr0 : Reach (2048*q+1653) (4096*q+3305) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1653_0 q hr0

#print axioms blank_halt_not_1653_mod2048

/-- Exact inverse-tree certificate for the all-natural 1745 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1745_11 (q : Nat) :
    ¬ Reach (1104*q+932) (5984*q+5078) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (1104*q+932) (5984*q+5078) hn (by omega) (by omega)
  omega

private theorem no_1745_10 (q : Nat) :
    ¬ Reach (2208*q+1867) (3776*q+3211) := by
  intro hr
  rcases odd_back (2208*q+1867) (3776*q+3211) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1104*q+932 := by omega
    have ye : y = 5984*q+5078 := by omega
    rw [xe,ye] at hp
    exact no_1745_11 q hp
  · omega

private theorem no_1745_9 (q : Nat) :
    ¬ Reach (40*q+31) (8112*q+6885) := by
  intro hr
  have ha := reach_allowed (40*q+31) (8112*q+6885) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1745_8 (q : Nat) :
    ¬ Reach (80*q+65) (8032*q+6820) := by
  intro hr
  rcases odd_back (80*q+65) (8032*q+6820) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 40*q+31 := by omega
    have ye : y = 8112*q+6885 := by omega
    rw [xe,ye] at hp
    exact no_1745_9 q hp
  · omega

private theorem no_1745_7 (q : Nat) :
    ¬ Reach (160*q+133) (7872*q+6687) := by
  intro hr
  rcases odd_back (160*q+133) (7872*q+6687) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 80*q+65 := by omega
    have ye : y = 8032*q+6820 := by omega
    rw [xe,ye] at hp
    exact no_1745_8 q hp
  · omega

private theorem no_1745_6 (q : Nat) :
    ¬ Reach (320*q+269) (7552*q+6418) := by
  intro hr
  rcases odd_back (320*q+269) (7552*q+6418) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 160*q+133 := by omega
    have ye : y = 7872*q+6687 := by omega
    rw [xe,ye] at hp
    exact no_1745_7 q hp
  · have xe : x = 2208*q+1867 := by omega
    have ye : y = 3776*q+3211 := by omega
    rw [xe,ye] at hp
    exact no_1745_10 q hp

private theorem no_1745_5 (q : Nat) :
    ¬ Reach (640*q+541) (6912*q+5877) := by
  intro hr
  rcases odd_back (640*q+541) (6912*q+5877) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 320*q+269 := by omega
    have ye : y = 7552*q+6418 := by omega
    rw [xe,ye] at hp
    exact no_1745_6 q hp
  · omega

private theorem no_1745_4 (q : Nat) :
    ¬ Reach (1280*q+1085) (5632*q+4792) := by
  intro hr
  rcases odd_back (1280*q+1085) (5632*q+4792) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 640*q+541 := by omega
    have ye : y = 6912*q+5877 := by omega
    rw [xe,ye] at hp
    exact no_1745_5 q hp
  · omega

private theorem no_1745_3 (q : Nat) :
    ¬ Reach (2560*q+2173) (3072*q+2619) := by
  intro hr
  rcases odd_back (2560*q+2173) (3072*q+2619) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+1085 := by omega
    have ye : y = 5632*q+4792 := by omega
    rw [xe,ye] at hp
    exact no_1745_4 q hp
  · omega

private theorem no_1745_2 (q : Nat) :
    ¬ Reach (512*q+434) (7168*q+6105) := by
  intro hr
  have ha := reach_allowed (512*q+434) (7168*q+6105) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1745_1 (q : Nat) :
    ¬ Reach (1024*q+871) (6144*q+5234) := by
  intro hr
  rcases odd_back (1024*q+871) (6144*q+5234) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+434 := by omega
    have ye : y = 7168*q+6105 := by omega
    rw [xe,ye] at hp
    exact no_1745_2 q hp
  · have xe : x = 2560*q+2173 := by omega
    have ye : y = 3072*q+2619 := by omega
    rw [xe,ye] at hp
    exact no_1745_3 q hp

private theorem no_1745_0 (q : Nat) :
    ¬ Reach (2048*q+1745) (4096*q+3489) := by
  intro hr
  rcases odd_back (2048*q+1745) (4096*q+3489) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+871 := by omega
    have ye : y = 6144*q+5234 := by omega
    rw [xe,ye] at hp
    exact no_1745_1 q hp
  · omega

theorem blank_halt_not_1745_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1745 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1745 := by dsimp [q]; omega
  have hb : b=4096*q+3489 := by omega
  have hr0 : Reach (2048*q+1745) (4096*q+3489) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1745_0 q hr0

#print axioms blank_halt_not_1745_mod2048

/-- Exact inverse-tree certificate for the all-natural 1845 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1845_8 (q : Nat) :
    ¬ Reach (2560*q+2298) (3072*q+2769) := by
  intro hr
  have ha := reach_allowed (2560*q+2298) (3072*q+2769) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1845_7 (q : Nat) :
    ¬ Reach (2592*q+2321) (3008*q+2707) := by
  intro hr
  have ha := reach_allowed (2592*q+2321) (3008*q+2707) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1845_6 (q : Nat) :
    ¬ Reach (544*q+486) (7104*q+6385) := by
  intro hr
  have ha := reach_allowed (544*q+486) (7104*q+6385) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1845_5 (q : Nat) :
    ¬ Reach (1088*q+975) (6016*q+5410) := by
  intro hr
  rcases odd_back (1088*q+975) (6016*q+5410) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+486 := by omega
    have ye : y = 7104*q+6385 := by omega
    rw [xe,ye] at hp
    exact no_1845_6 q hp
  · have xe : x = 2592*q+2321 := by omega
    have ye : y = 3008*q+2707 := by omega
    rw [xe,ye] at hp
    exact no_1845_7 q hp

private theorem no_1845_4 (q : Nat) :
    ¬ Reach (2176*q+1953) (3840*q+3457) := by
  intro hr
  rcases odd_back (2176*q+1953) (3840*q+3457) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+975 := by omega
    have ye : y = 6016*q+5410 := by omega
    rw [xe,ye] at hp
    exact no_1845_5 q hp
  · omega

private theorem no_1845_3 (q : Nat) :
    ¬ Reach (256*q+228) (7680*q+6914) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+228) (7680*q+6914) (by omega) (by omega) hr
  have xe : x = 2176*q+1953 := by omega
  have ye : y = 3840*q+3457 := by omega
  rw [xe,ye] at hp
  exact no_1845_4 q hp

private theorem no_1845_2 (q : Nat) :
    ¬ Reach (512*q+459) (7168*q+6455) := by
  intro hr
  rcases odd_back (512*q+459) (7168*q+6455) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+228 := by omega
    have ye : y = 7680*q+6914 := by omega
    rw [xe,ye] at hp
    exact no_1845_3 q hp
  · omega

private theorem no_1845_1 (q : Nat) :
    ¬ Reach (1024*q+921) (6144*q+5534) := by
  intro hr
  rcases odd_back (1024*q+921) (6144*q+5534) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+459 := by omega
    have ye : y = 7168*q+6455 := by omega
    rw [xe,ye] at hp
    exact no_1845_2 q hp
  · have xe : x = 2560*q+2298 := by omega
    have ye : y = 3072*q+2769 := by omega
    rw [xe,ye] at hp
    exact no_1845_8 q hp

private theorem no_1845_0 (q : Nat) :
    ¬ Reach (2048*q+1845) (4096*q+3689) := by
  intro hr
  rcases odd_back (2048*q+1845) (4096*q+3689) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+921 := by omega
    have ye : y = 6144*q+5534 := by omega
    rw [xe,ye] at hp
    exact no_1845_1 q hp
  · omega

theorem blank_halt_not_1845_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1845 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1845 := by dsimp [q]; omega
  have hb : b=4096*q+3689 := by omega
  have hr0 : Reach (2048*q+1845) (4096*q+3689) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1845_0 q hr0

#print axioms blank_halt_not_1845_mod2048

/-- Exact inverse-tree certificate for the all-natural 1865 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1865_5 (q : Nat) :
    ¬ Reach (2688*q+2437) (2816*q+2561) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod32.rooted_not_5_1 n (2688*q+2437) (2816*q+2561) hn (by omega)
  omega

private theorem no_1865_4 (q : Nat) :
    ¬ Reach (1280*q+1160) (5632*q+5122) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+1160) (5632*q+5122) (by omega) (by omega) hr
  have xe : x = 2688*q+2437 := by omega
  have ye : y = 2816*q+2561 := by omega
  rw [xe,ye] at hp
  exact no_1865_5 q hp

private theorem no_1865_3 (q : Nat) :
    ¬ Reach (2560*q+2323) (3072*q+2799) := by
  intro hr
  rcases odd_back (2560*q+2323) (3072*q+2799) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+1160 := by omega
    have ye : y = 5632*q+5122 := by omega
    rw [xe,ye] at hp
    exact no_1865_4 q hp
  · omega

private theorem no_1865_2 (q : Nat) :
    ¬ Reach (512*q+464) (7168*q+6525) := by
  intro hr
  have ha := reach_allowed (512*q+464) (7168*q+6525) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1865_1 (q : Nat) :
    ¬ Reach (1024*q+931) (6144*q+5594) := by
  intro hr
  rcases odd_back (1024*q+931) (6144*q+5594) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+464 := by omega
    have ye : y = 7168*q+6525 := by omega
    rw [xe,ye] at hp
    exact no_1865_2 q hp
  · have xe : x = 2560*q+2323 := by omega
    have ye : y = 3072*q+2799 := by omega
    rw [xe,ye] at hp
    exact no_1865_3 q hp

private theorem no_1865_0 (q : Nat) :
    ¬ Reach (2048*q+1865) (4096*q+3729) := by
  intro hr
  rcases odd_back (2048*q+1865) (4096*q+3729) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+931 := by omega
    have ye : y = 6144*q+5594 := by omega
    rw [xe,ye] at hp
    exact no_1865_1 q hp
  · omega

theorem blank_halt_not_1865_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1865 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1865 := by dsimp [q]; omega
  have hb : b=4096*q+3729 := by omega
  have hr0 : Reach (2048*q+1865) (4096*q+3729) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1865_0 q hr0

#print axioms blank_halt_not_1865_mod2048

/-- Exact inverse-tree certificate for the all-natural 1909 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1909_6 (q : Nat) :
    ¬ Reach (2560*q+2378) (3072*q+2865) := by
  intro hr
  have ha := reach_allowed (2560*q+2378) (3072*q+2865) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1909_5 (q : Nat) :
    ¬ Reach (1088*q+1009) (6016*q+5598) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_1_6 n (1088*q+1009) (6016*q+5598) hn (by omega)
  omega

private theorem no_1909_4 (q : Nat) :
    ¬ Reach (2176*q+2021) (3840*q+3577) := by
  intro hr
  rcases odd_back (2176*q+2021) (3840*q+3577) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+1009 := by omega
    have ye : y = 6016*q+5598 := by omega
    rw [xe,ye] at hp
    exact no_1909_5 q hp
  · omega

private theorem no_1909_3 (q : Nat) :
    ¬ Reach (256*q+236) (7680*q+7154) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+236) (7680*q+7154) (by omega) (by omega) hr
  have xe : x = 2176*q+2021 := by omega
  have ye : y = 3840*q+3577 := by omega
  rw [xe,ye] at hp
  exact no_1909_4 q hp

private theorem no_1909_2 (q : Nat) :
    ¬ Reach (512*q+475) (7168*q+6679) := by
  intro hr
  rcases odd_back (512*q+475) (7168*q+6679) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+236 := by omega
    have ye : y = 7680*q+7154 := by omega
    rw [xe,ye] at hp
    exact no_1909_3 q hp
  · omega

private theorem no_1909_1 (q : Nat) :
    ¬ Reach (1024*q+953) (6144*q+5726) := by
  intro hr
  rcases odd_back (1024*q+953) (6144*q+5726) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+475 := by omega
    have ye : y = 7168*q+6679 := by omega
    rw [xe,ye] at hp
    exact no_1909_2 q hp
  · have xe : x = 2560*q+2378 := by omega
    have ye : y = 3072*q+2865 := by omega
    rw [xe,ye] at hp
    exact no_1909_6 q hp

private theorem no_1909_0 (q : Nat) :
    ¬ Reach (2048*q+1909) (4096*q+3817) := by
  intro hr
  rcases odd_back (2048*q+1909) (4096*q+3817) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+953 := by omega
    have ye : y = 6144*q+5726 := by omega
    rw [xe,ye] at hp
    exact no_1909_1 q hp
  · omega

theorem blank_halt_not_1909_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1909 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1909 := by dsimp [q]; omega
  have hb : b=4096*q+3817 := by omega
  have hr0 : Reach (2048*q+1909) (4096*q+3817) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1909_0 q hr0

#print axioms blank_halt_not_1909_mod2048

/-- Exact inverse-tree certificate for the all-natural 1993 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1993_6 (q : Nat) :
    ¬ Reach (1344*q+1301) (5504*q+5342) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_5_6 n (1344*q+1301) (5504*q+5342) hn (by omega)
  omega

private theorem no_1993_5 (q : Nat) :
    ¬ Reach (2688*q+2605) (2816*q+2737) := by
  intro hr
  rcases odd_back (2688*q+2605) (2816*q+2737) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+1301 := by omega
    have ye : y = 5504*q+5342 := by omega
    rw [xe,ye] at hp
    exact no_1993_6 q hp
  · omega

private theorem no_1993_4 (q : Nat) :
    ¬ Reach (1280*q+1240) (5632*q+5474) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+1240) (5632*q+5474) (by omega) (by omega) hr
  have xe : x = 2688*q+2605 := by omega
  have ye : y = 2816*q+2737 := by omega
  rw [xe,ye] at hp
  exact no_1993_5 q hp

private theorem no_1993_3 (q : Nat) :
    ¬ Reach (2560*q+2483) (3072*q+2991) := by
  intro hr
  rcases odd_back (2560*q+2483) (3072*q+2991) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+1240 := by omega
    have ye : y = 5632*q+5474 := by omega
    rw [xe,ye] at hp
    exact no_1993_4 q hp
  · omega

private theorem no_1993_2 (q : Nat) :
    ¬ Reach (512*q+496) (7168*q+6973) := by
  intro hr
  have ha := reach_allowed (512*q+496) (7168*q+6973) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1993_1 (q : Nat) :
    ¬ Reach (1024*q+995) (6144*q+5978) := by
  intro hr
  rcases odd_back (1024*q+995) (6144*q+5978) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+496 := by omega
    have ye : y = 7168*q+6973 := by omega
    rw [xe,ye] at hp
    exact no_1993_2 q hp
  · have xe : x = 2560*q+2483 := by omega
    have ye : y = 3072*q+2991 := by omega
    rw [xe,ye] at hp
    exact no_1993_3 q hp

private theorem no_1993_0 (q : Nat) :
    ¬ Reach (2048*q+1993) (4096*q+3985) := by
  intro hr
  rcases odd_back (2048*q+1993) (4096*q+3985) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+995 := by omega
    have ye : y = 6144*q+5978 := by omega
    rw [xe,ye] at hp
    exact no_1993_1 q hp
  · omega

theorem blank_halt_not_1993_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1993 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1993 := by dsimp [q]; omega
  have hb : b=4096*q+3985 := by omega
  have hr0 : Reach (2048*q+1993) (4096*q+3985) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1993_0 q hr0

#print axioms blank_halt_not_1993_mod2048

/-- Exact inverse-tree certificate for the all-natural 2037 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_2037_6 (q : Nat) :
    ¬ Reach (2560*q+2538) (3072*q+3057) := by
  intro hr
  have ha := reach_allowed (2560*q+2538) (3072*q+3057) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_2037_5 (q : Nat) :
    ¬ Reach (1088*q+1077) (6016*q+5974) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_5_6 n (1088*q+1077) (6016*q+5974) hn (by omega)
  omega

private theorem no_2037_4 (q : Nat) :
    ¬ Reach (2176*q+2157) (3840*q+3817) := by
  intro hr
  rcases odd_back (2176*q+2157) (3840*q+3817) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+1077 := by omega
    have ye : y = 6016*q+5974 := by omega
    rw [xe,ye] at hp
    exact no_2037_5 q hp
  · omega

private theorem no_2037_3 (q : Nat) :
    ¬ Reach (256*q+252) (7680*q+7634) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+252) (7680*q+7634) (by omega) (by omega) hr
  have xe : x = 2176*q+2157 := by omega
  have ye : y = 3840*q+3817 := by omega
  rw [xe,ye] at hp
  exact no_2037_4 q hp

private theorem no_2037_2 (q : Nat) :
    ¬ Reach (512*q+507) (7168*q+7127) := by
  intro hr
  rcases odd_back (512*q+507) (7168*q+7127) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+252 := by omega
    have ye : y = 7680*q+7634 := by omega
    rw [xe,ye] at hp
    exact no_2037_3 q hp
  · omega

private theorem no_2037_1 (q : Nat) :
    ¬ Reach (1024*q+1017) (6144*q+6110) := by
  intro hr
  rcases odd_back (1024*q+1017) (6144*q+6110) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+507 := by omega
    have ye : y = 7168*q+7127 := by omega
    rw [xe,ye] at hp
    exact no_2037_2 q hp
  · have xe : x = 2560*q+2538 := by omega
    have ye : y = 3072*q+3057 := by omega
    rw [xe,ye] at hp
    exact no_2037_6 q hp

private theorem no_2037_0 (q : Nat) :
    ¬ Reach (2048*q+2037) (4096*q+4073) := by
  intro hr
  rcases odd_back (2048*q+2037) (4096*q+4073) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+1017 := by omega
    have ye : y = 6144*q+6110 := by omega
    rw [xe,ye] at hp
    exact no_2037_1 q hp
  · omega

theorem blank_halt_not_2037_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠2037 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+2037 := by dsimp [q]; omega
  have hb : b=4096*q+4073 := by omega
  have hr0 : Reach (2048*q+2037) (4096*q+4073) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_2037_0 q hr0

#print axioms blank_halt_not_2037_mod2048

end BB429AutoGroup4

import BB429No11Odd
import BB429NewResidue
import BB429RootMod32
import Lean.Elab.Tactic.Omega

namespace BB429Shift53And721
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

private theorem no_53_fixed_3 (q : Nat) :
    ¬ Reach (0*q+58) (0*q+81) := by
  intro hr
  have ha := reach_allowed (0*q+58) (0*q+81) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_53_fixed_2 (q : Nat) :
    ¬ Reach (0*q+11) (0*q+183) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have he := BB429No11Odd.rooted_eleven_even n (0*q+183) (by simpa using hn)
  omega

private theorem no_53_fixed_1 (q : Nat) :
    ¬ Reach (0*q+25) (0*q+158) := by
  intro hr
  rcases odd_back (0*q+25) (0*q+158) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+11 := by omega
    have ye : y = 0*q+183 := by omega
    rw [xe,ye] at hp
    exact no_53_fixed_2 q hp
  · have xe : x = 0*q+58 := by omega
    have ye : y = 0*q+81 := by omega
    rw [xe,ye] at hp
    exact no_53_fixed_3 q hp

private theorem no_53_fixed_0 (q : Nat) :
    ¬ Reach (0*q+53) (0*q+105) := by
  intro hr
  rcases odd_back (0*q+53) (0*q+105) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+25 := by omega
    have ye : y = 0*q+158 := by omega
    rw [xe,ye] at hp
    exact no_53_fixed_1 q hp
  · omega

private theorem no_53_shift_11 (q : Nat) :
    ¬ Reach (2560*q+2618) (3072*q+3153) := by
  intro hr
  have ha := reach_allowed (2560*q+2618) (3072*q+3153) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_53_shift_10 (q : Nat) :
    ¬ Reach (324*q+328) (7544*q+7708) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (324*q+328) (7544*q+7708) hn (by omega) (by omega)
  omega

private theorem no_53_shift_9 (q : Nat) :
    ¬ Reach (648*q+659) (6896*q+7049) := by
  intro hr
  rcases odd_back (648*q+659) (6896*q+7049) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 324*q+328 := by omega
    have ye : y = 7544*q+7708 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_10 q hp
  · omega

private theorem no_53_shift_8 (q : Nat) :
    ¬ Reach (1296*q+1321) (5600*q+5728) := by
  intro hr
  rcases odd_back (1296*q+1321) (5600*q+5728) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 648*q+659 := by omega
    have ye : y = 6896*q+7049 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_9 q hp
  · omega

private theorem no_53_shift_7 (q : Nat) :
    ¬ Reach (2592*q+2645) (3008*q+3083) := by
  intro hr
  rcases odd_back (2592*q+2645) (3008*q+3083) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1296*q+1321 := by omega
    have ye : y = 5600*q+5728 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_8 q hp
  · omega

private theorem no_53_shift_6 (q : Nat) :
    ¬ Reach (544*q+554) (7104*q+7273) := by
  intro hr
  have ha := reach_allowed (544*q+554) (7104*q+7273) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_53_shift_5 (q : Nat) :
    ¬ Reach (1088*q+1111) (6016*q+6162) := by
  intro hr
  rcases odd_back (1088*q+1111) (6016*q+6162) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+554 := by omega
    have ye : y = 7104*q+7273 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_6 q hp
  · have xe : x = 2592*q+2645 := by omega
    have ye : y = 3008*q+3083 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_7 q hp

private theorem no_53_shift_4 (q : Nat) :
    ¬ Reach (2176*q+2225) (3840*q+3937) := by
  intro hr
  rcases odd_back (2176*q+2225) (3840*q+3937) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+1111 := by omega
    have ye : y = 6016*q+6162 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_5 q hp
  · omega

private theorem no_53_shift_3 (q : Nat) :
    ¬ Reach (256*q+260) (7680*q+7874) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+260) (7680*q+7874) (by omega) (by omega) hr
  have xe : x = 2176*q+2225 := by omega
  have ye : y = 3840*q+3937 := by omega
  rw [xe,ye] at hp
  exact no_53_shift_4 q hp

private theorem no_53_shift_2 (q : Nat) :
    ¬ Reach (512*q+523) (7168*q+7351) := by
  intro hr
  rcases odd_back (512*q+523) (7168*q+7351) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+260 := by omega
    have ye : y = 7680*q+7874 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_3 q hp
  · omega

private theorem no_53_shift_1 (q : Nat) :
    ¬ Reach (1024*q+1049) (6144*q+6302) := by
  intro hr
  rcases odd_back (1024*q+1049) (6144*q+6302) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+523 := by omega
    have ye : y = 7168*q+7351 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_2 q hp
  · have xe : x = 2560*q+2618 := by omega
    have ye : y = 3072*q+3153 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_11 q hp

private theorem no_53_shift_0 (q : Nat) :
    ¬ Reach (2048*q+2101) (4096*q+4201) := by
  intro hr
  rcases odd_back (2048*q+2101) (4096*q+4201) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+1049 := by omega
    have ye : y = 6144*q+6302 := by omega
    rw [xe,ye] at hp
    exact no_53_shift_1 q hp
  · omega

private theorem no_53_whole (q : Nat) :
    ¬ Reach (2048*q+53) (4096*q+105) := by
  cases q with
  | zero =>
    simpa using no_53_fixed_0 0
  | succ t =>
    intro hr
    have hp : Reach (2048*t+2101) (4096*t+4201) := by
      have hu : 2048*(t+1)+53 = 2048*t+2101 := by omega
      have hw : 4096*(t+1)+105 = 4096*t+4201 := by omega
      simpa only [hu,hw] using hr
    exact no_53_shift_0 t hp

theorem blank_halt_not_53_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%2048≠53 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+53 := by dsimp [q]; omega
  have hb : b=4096*q+105 := by omega
  have hr0 : Reach (2048*q+53) (4096*q+105) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_53_whole q hr0

#print axioms blank_halt_not_53_mod2048

private theorem no_721_fixed_11 (q : Nat) :
    ¬ Reach (0*q+380) (0*q+2086) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (0*q+380) (0*q+2086) hn (by omega) (by omega)
  omega

private theorem no_721_fixed_10 (q : Nat) :
    ¬ Reach (0*q+763) (0*q+1323) := by
  intro hr
  rcases odd_back (0*q+763) (0*q+1323) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+380 := by omega
    have ye : y = 0*q+2086 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_11 q hp
  · omega

private theorem no_721_fixed_9 (q : Nat) :
    ¬ Reach (0*q+11) (0*q+2829) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have he := BB429No11Odd.rooted_eleven_even n (0*q+2829) (by simpa using hn)
  omega

private theorem no_721_fixed_8 (q : Nat) :
    ¬ Reach (0*q+25) (0*q+2804) := by
  intro hr
  rcases odd_back (0*q+25) (0*q+2804) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+11 := by omega
    have ye : y = 0*q+2829 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_9 q hp
  · omega

private theorem no_721_fixed_7 (q : Nat) :
    ¬ Reach (0*q+53) (0*q+2751) := by
  intro hr
  rcases odd_back (0*q+53) (0*q+2751) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+25 := by omega
    have ye : y = 0*q+2804 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_8 q hp
  · omega

private theorem no_721_fixed_6 (q : Nat) :
    ¬ Reach (0*q+109) (0*q+2642) := by
  intro hr
  rcases odd_back (0*q+109) (0*q+2642) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+53 := by omega
    have ye : y = 0*q+2751 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_7 q hp
  · have xe : x = 0*q+763 := by omega
    have ye : y = 0*q+1323 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_10 q hp

private theorem no_721_fixed_5 (q : Nat) :
    ¬ Reach (0*q+221) (0*q+2421) := by
  intro hr
  rcases odd_back (0*q+221) (0*q+2421) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+109 := by omega
    have ye : y = 0*q+2642 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_6 q hp
  · omega

private theorem no_721_fixed_4 (q : Nat) :
    ¬ Reach (0*q+445) (0*q+1976) := by
  intro hr
  rcases odd_back (0*q+445) (0*q+1976) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+221 := by omega
    have ye : y = 0*q+2421 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_5 q hp
  · omega

private theorem no_721_fixed_3 (q : Nat) :
    ¬ Reach (0*q+893) (0*q+1083) := by
  intro hr
  rcases odd_back (0*q+893) (0*q+1083) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+445 := by omega
    have ye : y = 0*q+1976 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_4 q hp
  · omega

private theorem no_721_fixed_2 (q : Nat) :
    ¬ Reach (0*q+178) (0*q+2521) := by
  intro hr
  have ha := reach_allowed (0*q+178) (0*q+2521) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_721_fixed_1 (q : Nat) :
    ¬ Reach (0*q+359) (0*q+2162) := by
  intro hr
  rcases odd_back (0*q+359) (0*q+2162) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+178 := by omega
    have ye : y = 0*q+2521 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_2 q hp
  · have xe : x = 0*q+893 := by omega
    have ye : y = 0*q+1083 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_3 q hp

private theorem no_721_fixed_0 (q : Nat) :
    ¬ Reach (0*q+721) (0*q+1441) := by
  intro hr
  rcases odd_back (0*q+721) (0*q+1441) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 0*q+359 := by omega
    have ye : y = 0*q+2162 := by omega
    rw [xe,ye] at hp
    exact no_721_fixed_1 q hp
  · omega

private theorem no_721_shift_12 (q : Nat) :
    ¬ Reach (1104*q+1484) (5984*q+8070) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (1104*q+1484) (5984*q+8070) hn (by omega) (by omega)
  omega

private theorem no_721_shift_11 (q : Nat) :
    ¬ Reach (2208*q+2971) (3776*q+5099) := by
  intro hr
  rcases odd_back (2208*q+2971) (3776*q+5099) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1104*q+1484 := by omega
    have ye : y = 5984*q+8070 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_12 q hp
  · omega

private theorem no_721_shift_10 (q : Nat) :
    ¬ Reach (20*q+24) (8152*q+10992) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (20*q+24) (8152*q+10992) hn (by omega) (by omega)
  omega

private theorem no_721_shift_9 (q : Nat) :
    ¬ Reach (40*q+51) (8112*q+10941) := by
  intro hr
  rcases odd_back (40*q+51) (8112*q+10941) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 20*q+24 := by omega
    have ye : y = 8152*q+10992 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_10 q hp
  · omega

private theorem no_721_shift_8 (q : Nat) :
    ¬ Reach (80*q+105) (8032*q+10836) := by
  intro hr
  rcases odd_back (80*q+105) (8032*q+10836) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 40*q+51 := by omega
    have ye : y = 8112*q+10941 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_9 q hp
  · omega

private theorem no_721_shift_7 (q : Nat) :
    ¬ Reach (160*q+213) (7872*q+10623) := by
  intro hr
  rcases odd_back (160*q+213) (7872*q+10623) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 80*q+105 := by omega
    have ye : y = 8032*q+10836 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_8 q hp
  · omega

private theorem no_721_shift_6 (q : Nat) :
    ¬ Reach (320*q+429) (7552*q+10194) := by
  intro hr
  rcases odd_back (320*q+429) (7552*q+10194) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 160*q+213 := by omega
    have ye : y = 7872*q+10623 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_7 q hp
  · have xe : x = 2208*q+2971 := by omega
    have ye : y = 3776*q+5099 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_11 q hp

private theorem no_721_shift_5 (q : Nat) :
    ¬ Reach (640*q+861) (6912*q+9333) := by
  intro hr
  rcases odd_back (640*q+861) (6912*q+9333) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 320*q+429 := by omega
    have ye : y = 7552*q+10194 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_6 q hp
  · omega

private theorem no_721_shift_4 (q : Nat) :
    ¬ Reach (1280*q+1725) (5632*q+7608) := by
  intro hr
  rcases odd_back (1280*q+1725) (5632*q+7608) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 640*q+861 := by omega
    have ye : y = 6912*q+9333 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_5 q hp
  · omega

private theorem no_721_shift_3 (q : Nat) :
    ¬ Reach (2560*q+3453) (3072*q+4155) := by
  intro hr
  rcases odd_back (2560*q+3453) (3072*q+4155) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+1725 := by omega
    have ye : y = 5632*q+7608 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_4 q hp
  · omega

private theorem no_721_shift_2 (q : Nat) :
    ¬ Reach (512*q+690) (7168*q+9689) := by
  intro hr
  have ha := reach_allowed (512*q+690) (7168*q+9689) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_721_shift_1 (q : Nat) :
    ¬ Reach (1024*q+1383) (6144*q+8306) := by
  intro hr
  rcases odd_back (1024*q+1383) (6144*q+8306) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+690 := by omega
    have ye : y = 7168*q+9689 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_2 q hp
  · have xe : x = 2560*q+3453 := by omega
    have ye : y = 3072*q+4155 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_3 q hp

private theorem no_721_shift_0 (q : Nat) :
    ¬ Reach (2048*q+2769) (4096*q+5537) := by
  intro hr
  rcases odd_back (2048*q+2769) (4096*q+5537) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+1383 := by omega
    have ye : y = 6144*q+8306 := by omega
    rw [xe,ye] at hp
    exact no_721_shift_1 q hp
  · omega

private theorem no_721_whole (q : Nat) :
    ¬ Reach (2048*q+721) (4096*q+1441) := by
  cases q with
  | zero =>
    simpa using no_721_fixed_0 0
  | succ t =>
    intro hr
    have hp : Reach (2048*t+2769) (4096*t+5537) := by
      have hu : 2048*(t+1)+721 = 2048*t+2769 := by omega
      have hw : 4096*(t+1)+1441 = 4096*t+5537 := by omega
      simpa only [hu,hw] using hr
    exact no_721_shift_0 t hp

theorem blank_halt_not_721_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%2048≠721 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+721 := by dsimp [q]; omega
  have hb : b=4096*q+1441 := by omega
  have hr0 : Reach (2048*q+721) (4096*q+1441) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_721_whole q hr0

#print axioms blank_halt_not_721_mod2048

end BB429Shift53And721

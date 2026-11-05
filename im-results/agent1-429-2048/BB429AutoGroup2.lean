import BB429RootMod32
import BB429NewResidue
import Lean.Elab.Tactic.Omega

namespace BB429AutoGroup2
open BB429NewResidue

set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Exact inverse-tree certificate for the all-natural 757 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_757_10 (q : Nat) :
    ¬ Reach (2560*q+938) (3072*q+1137) := by
  intro hr
  have ha := reach_allowed (2560*q+938) (3072*q+1137) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_757_9 (q : Nat) :
    ¬ Reach (2592*q+944) (3008*q+1109) := by
  intro hr
  have ha := reach_allowed (2592*q+944) (3008*q+1109) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_757_8 (q : Nat) :
    ¬ Reach (136*q+47) (7920*q+2905) := by
  intro hr
  have ha := reach_allowed (136*q+47) (7920*q+2905) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_757_7 (q : Nat) :
    ¬ Reach (272*q+97) (7648*q+2808) := by
  intro hr
  rcases odd_back (272*q+97) (7648*q+2808) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 136*q+47 := by omega
    have ye : y = 7920*q+2905 := by omega
    rw [xe,ye] at hp
    exact no_757_8 q hp
  · omega

private theorem no_757_6 (q : Nat) :
    ¬ Reach (544*q+197) (7104*q+2611) := by
  intro hr
  rcases odd_back (544*q+197) (7104*q+2611) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 272*q+97 := by omega
    have ye : y = 7648*q+2808 := by omega
    rw [xe,ye] at hp
    exact no_757_7 q hp
  · omega

private theorem no_757_5 (q : Nat) :
    ¬ Reach (1088*q+397) (6016*q+2214) := by
  intro hr
  rcases odd_back (1088*q+397) (6016*q+2214) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+197 := by omega
    have ye : y = 7104*q+2611 := by omega
    rw [xe,ye] at hp
    exact no_757_6 q hp
  · have xe : x = 2592*q+944 := by omega
    have ye : y = 3008*q+1109 := by omega
    rw [xe,ye] at hp
    exact no_757_9 q hp

private theorem no_757_4 (q : Nat) :
    ¬ Reach (2176*q+797) (3840*q+1417) := by
  intro hr
  rcases odd_back (2176*q+797) (3840*q+1417) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+397 := by omega
    have ye : y = 6016*q+2214 := by omega
    rw [xe,ye] at hp
    exact no_757_5 q hp
  · omega

private theorem no_757_3 (q : Nat) :
    ¬ Reach (256*q+92) (7680*q+2834) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+92) (7680*q+2834) (by omega) (by omega) hr
  have xe : x = 2176*q+797 := by omega
  have ye : y = 3840*q+1417 := by omega
  rw [xe,ye] at hp
  exact no_757_4 q hp

private theorem no_757_2 (q : Nat) :
    ¬ Reach (512*q+187) (7168*q+2647) := by
  intro hr
  rcases odd_back (512*q+187) (7168*q+2647) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+92 := by omega
    have ye : y = 7680*q+2834 := by omega
    rw [xe,ye] at hp
    exact no_757_3 q hp
  · omega

private theorem no_757_1 (q : Nat) :
    ¬ Reach (1024*q+377) (6144*q+2270) := by
  intro hr
  rcases odd_back (1024*q+377) (6144*q+2270) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+187 := by omega
    have ye : y = 7168*q+2647 := by omega
    rw [xe,ye] at hp
    exact no_757_2 q hp
  · have xe : x = 2560*q+938 := by omega
    have ye : y = 3072*q+1137 := by omega
    rw [xe,ye] at hp
    exact no_757_10 q hp

private theorem no_757_0 (q : Nat) :
    ¬ Reach (2048*q+757) (4096*q+1513) := by
  intro hr
  rcases odd_back (2048*q+757) (4096*q+1513) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+377 := by omega
    have ye : y = 6144*q+2270 := by omega
    rw [xe,ye] at hp
    exact no_757_1 q hp
  · omega

theorem blank_halt_not_757_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠757 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+757 := by dsimp [q]; omega
  have hb : b=4096*q+1513 := by omega
  have hr0 : Reach (2048*q+757) (4096*q+1513) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_757_0 q hr0

#print axioms blank_halt_not_757_mod2048

/-- Exact inverse-tree certificate for the all-natural 821 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_821_8 (q : Nat) :
    ¬ Reach (2560*q+1018) (3072*q+1233) := by
  intro hr
  have ha := reach_allowed (2560*q+1018) (3072*q+1233) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_821_7 (q : Nat) :
    ¬ Reach (2592*q+1025) (3008*q+1203) := by
  intro hr
  have ha := reach_allowed (2592*q+1025) (3008*q+1203) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_821_6 (q : Nat) :
    ¬ Reach (544*q+214) (7104*q+2833) := by
  intro hr
  have ha := reach_allowed (544*q+214) (7104*q+2833) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_821_5 (q : Nat) :
    ¬ Reach (1088*q+431) (6016*q+2402) := by
  intro hr
  rcases odd_back (1088*q+431) (6016*q+2402) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+214 := by omega
    have ye : y = 7104*q+2833 := by omega
    rw [xe,ye] at hp
    exact no_821_6 q hp
  · have xe : x = 2592*q+1025 := by omega
    have ye : y = 3008*q+1203 := by omega
    rw [xe,ye] at hp
    exact no_821_7 q hp

private theorem no_821_4 (q : Nat) :
    ¬ Reach (2176*q+865) (3840*q+1537) := by
  intro hr
  rcases odd_back (2176*q+865) (3840*q+1537) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+431 := by omega
    have ye : y = 6016*q+2402 := by omega
    rw [xe,ye] at hp
    exact no_821_5 q hp
  · omega

private theorem no_821_3 (q : Nat) :
    ¬ Reach (256*q+100) (7680*q+3074) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+100) (7680*q+3074) (by omega) (by omega) hr
  have xe : x = 2176*q+865 := by omega
  have ye : y = 3840*q+1537 := by omega
  rw [xe,ye] at hp
  exact no_821_4 q hp

private theorem no_821_2 (q : Nat) :
    ¬ Reach (512*q+203) (7168*q+2871) := by
  intro hr
  rcases odd_back (512*q+203) (7168*q+2871) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+100 := by omega
    have ye : y = 7680*q+3074 := by omega
    rw [xe,ye] at hp
    exact no_821_3 q hp
  · omega

private theorem no_821_1 (q : Nat) :
    ¬ Reach (1024*q+409) (6144*q+2462) := by
  intro hr
  rcases odd_back (1024*q+409) (6144*q+2462) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+203 := by omega
    have ye : y = 7168*q+2871 := by omega
    rw [xe,ye] at hp
    exact no_821_2 q hp
  · have xe : x = 2560*q+1018 := by omega
    have ye : y = 3072*q+1233 := by omega
    rw [xe,ye] at hp
    exact no_821_8 q hp

private theorem no_821_0 (q : Nat) :
    ¬ Reach (2048*q+821) (4096*q+1641) := by
  intro hr
  rcases odd_back (2048*q+821) (4096*q+1641) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+409 := by omega
    have ye : y = 6144*q+2462 := by omega
    rw [xe,ye] at hp
    exact no_821_1 q hp
  · omega

theorem blank_halt_not_821_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠821 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+821 := by dsimp [q]; omega
  have hb : b=4096*q+1641 := by omega
  have hr0 : Reach (2048*q+821) (4096*q+1641) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_821_0 q hr0

#print axioms blank_halt_not_821_mod2048

/-- Exact inverse-tree certificate for the all-natural 841 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_841_5 (q : Nat) :
    ¬ Reach (2688*q+1093) (2816*q+1153) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod32.rooted_not_5_1 n (2688*q+1093) (2816*q+1153) hn (by omega)
  omega

private theorem no_841_4 (q : Nat) :
    ¬ Reach (1280*q+520) (5632*q+2306) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+520) (5632*q+2306) (by omega) (by omega) hr
  have xe : x = 2688*q+1093 := by omega
  have ye : y = 2816*q+1153 := by omega
  rw [xe,ye] at hp
  exact no_841_5 q hp

private theorem no_841_3 (q : Nat) :
    ¬ Reach (2560*q+1043) (3072*q+1263) := by
  intro hr
  rcases odd_back (2560*q+1043) (3072*q+1263) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+520 := by omega
    have ye : y = 5632*q+2306 := by omega
    rw [xe,ye] at hp
    exact no_841_4 q hp
  · omega

private theorem no_841_2 (q : Nat) :
    ¬ Reach (512*q+208) (7168*q+2941) := by
  intro hr
  have ha := reach_allowed (512*q+208) (7168*q+2941) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_841_1 (q : Nat) :
    ¬ Reach (1024*q+419) (6144*q+2522) := by
  intro hr
  rcases odd_back (1024*q+419) (6144*q+2522) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+208 := by omega
    have ye : y = 7168*q+2941 := by omega
    rw [xe,ye] at hp
    exact no_841_2 q hp
  · have xe : x = 2560*q+1043 := by omega
    have ye : y = 3072*q+1263 := by omega
    rw [xe,ye] at hp
    exact no_841_3 q hp

private theorem no_841_0 (q : Nat) :
    ¬ Reach (2048*q+841) (4096*q+1681) := by
  intro hr
  rcases odd_back (2048*q+841) (4096*q+1681) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+419 := by omega
    have ye : y = 6144*q+2522 := by omega
    rw [xe,ye] at hp
    exact no_841_1 q hp
  · omega

theorem blank_halt_not_841_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠841 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+841 := by dsimp [q]; omega
  have hb : b=4096*q+1681 := by omega
  have hr0 : Reach (2048*q+841) (4096*q+1681) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_841_0 q hr0

#print axioms blank_halt_not_841_mod2048

/-- Exact inverse-tree certificate for the all-natural 885 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_885_6 (q : Nat) :
    ¬ Reach (2560*q+1098) (3072*q+1329) := by
  intro hr
  have ha := reach_allowed (2560*q+1098) (3072*q+1329) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_885_5 (q : Nat) :
    ¬ Reach (1088*q+465) (6016*q+2590) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_1_6 n (1088*q+465) (6016*q+2590) hn (by omega)
  omega

private theorem no_885_4 (q : Nat) :
    ¬ Reach (2176*q+933) (3840*q+1657) := by
  intro hr
  rcases odd_back (2176*q+933) (3840*q+1657) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+465 := by omega
    have ye : y = 6016*q+2590 := by omega
    rw [xe,ye] at hp
    exact no_885_5 q hp
  · omega

private theorem no_885_3 (q : Nat) :
    ¬ Reach (256*q+108) (7680*q+3314) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+108) (7680*q+3314) (by omega) (by omega) hr
  have xe : x = 2176*q+933 := by omega
  have ye : y = 3840*q+1657 := by omega
  rw [xe,ye] at hp
  exact no_885_4 q hp

private theorem no_885_2 (q : Nat) :
    ¬ Reach (512*q+219) (7168*q+3095) := by
  intro hr
  rcases odd_back (512*q+219) (7168*q+3095) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+108 := by omega
    have ye : y = 7680*q+3314 := by omega
    rw [xe,ye] at hp
    exact no_885_3 q hp
  · omega

private theorem no_885_1 (q : Nat) :
    ¬ Reach (1024*q+441) (6144*q+2654) := by
  intro hr
  rcases odd_back (1024*q+441) (6144*q+2654) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+219 := by omega
    have ye : y = 7168*q+3095 := by omega
    rw [xe,ye] at hp
    exact no_885_2 q hp
  · have xe : x = 2560*q+1098 := by omega
    have ye : y = 3072*q+1329 := by omega
    rw [xe,ye] at hp
    exact no_885_6 q hp

private theorem no_885_0 (q : Nat) :
    ¬ Reach (2048*q+885) (4096*q+1769) := by
  intro hr
  rcases odd_back (2048*q+885) (4096*q+1769) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+441 := by omega
    have ye : y = 6144*q+2654 := by omega
    rw [xe,ye] at hp
    exact no_885_1 q hp
  · omega

theorem blank_halt_not_885_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠885 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+885 := by dsimp [q]; omega
  have hb : b=4096*q+1769 := by omega
  have hr0 : Reach (2048*q+885) (4096*q+1769) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_885_0 q hr0

#print axioms blank_halt_not_885_mod2048

/-- Exact inverse-tree certificate for the all-natural 969 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_969_6 (q : Nat) :
    ¬ Reach (1344*q+629) (5504*q+2590) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_5_6 n (1344*q+629) (5504*q+2590) hn (by omega)
  omega

private theorem no_969_5 (q : Nat) :
    ¬ Reach (2688*q+1261) (2816*q+1329) := by
  intro hr
  rcases odd_back (2688*q+1261) (2816*q+1329) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+629 := by omega
    have ye : y = 5504*q+2590 := by omega
    rw [xe,ye] at hp
    exact no_969_6 q hp
  · omega

private theorem no_969_4 (q : Nat) :
    ¬ Reach (1280*q+600) (5632*q+2658) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+600) (5632*q+2658) (by omega) (by omega) hr
  have xe : x = 2688*q+1261 := by omega
  have ye : y = 2816*q+1329 := by omega
  rw [xe,ye] at hp
  exact no_969_5 q hp

private theorem no_969_3 (q : Nat) :
    ¬ Reach (2560*q+1203) (3072*q+1455) := by
  intro hr
  rcases odd_back (2560*q+1203) (3072*q+1455) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+600 := by omega
    have ye : y = 5632*q+2658 := by omega
    rw [xe,ye] at hp
    exact no_969_4 q hp
  · omega

private theorem no_969_2 (q : Nat) :
    ¬ Reach (512*q+240) (7168*q+3389) := by
  intro hr
  have ha := reach_allowed (512*q+240) (7168*q+3389) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_969_1 (q : Nat) :
    ¬ Reach (1024*q+483) (6144*q+2906) := by
  intro hr
  rcases odd_back (1024*q+483) (6144*q+2906) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+240 := by omega
    have ye : y = 7168*q+3389 := by omega
    rw [xe,ye] at hp
    exact no_969_2 q hp
  · have xe : x = 2560*q+1203 := by omega
    have ye : y = 3072*q+1455 := by omega
    rw [xe,ye] at hp
    exact no_969_3 q hp

private theorem no_969_0 (q : Nat) :
    ¬ Reach (2048*q+969) (4096*q+1937) := by
  intro hr
  rcases odd_back (2048*q+969) (4096*q+1937) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+483 := by omega
    have ye : y = 6144*q+2906 := by omega
    rw [xe,ye] at hp
    exact no_969_1 q hp
  · omega

theorem blank_halt_not_969_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠969 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+969 := by dsimp [q]; omega
  have hb : b=4096*q+1937 := by omega
  have hr0 : Reach (2048*q+969) (4096*q+1937) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_969_0 q hr0

#print axioms blank_halt_not_969_mod2048

/-- Exact inverse-tree certificate for the all-natural 977 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_977_10 (q : Nat) :
    ¬ Reach (2600*q+1223) (2992*q+1417) := by
  intro hr
  have ha := reach_allowed (2600*q+1223) (2992*q+1417) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_977_9 (q : Nat) :
    ¬ Reach (1104*q+518) (5984*q+2834) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1104*q+518) (5984*q+2834) (by omega) (by omega) hr
  have xe : x = 2600*q+1223 := by omega
  have ye : y = 2992*q+1417 := by omega
  rw [xe,ye] at hp
  exact no_977_10 q hp

private theorem no_977_8 (q : Nat) :
    ¬ Reach (2208*q+1039) (3776*q+1795) := by
  intro hr
  rcases odd_back (2208*q+1039) (3776*q+1795) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1104*q+518 := by omega
    have ye : y = 5984*q+2834 := by omega
    rw [xe,ye] at hp
    exact no_977_9 q hp
  · omega

private theorem no_977_7 (q : Nat) :
    ¬ Reach (160*q+73) (7872*q+3735) := by
  intro hr
  have ha := reach_allowed (160*q+73) (7872*q+3735) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_977_6 (q : Nat) :
    ¬ Reach (320*q+149) (7552*q+3586) := by
  intro hr
  rcases odd_back (320*q+149) (7552*q+3586) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 160*q+73 := by omega
    have ye : y = 7872*q+3735 := by omega
    rw [xe,ye] at hp
    exact no_977_7 q hp
  · have xe : x = 2208*q+1039 := by omega
    have ye : y = 3776*q+1795 := by omega
    rw [xe,ye] at hp
    exact no_977_8 q hp

private theorem no_977_5 (q : Nat) :
    ¬ Reach (640*q+301) (6912*q+3285) := by
  intro hr
  rcases odd_back (640*q+301) (6912*q+3285) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 320*q+149 := by omega
    have ye : y = 7552*q+3586 := by omega
    rw [xe,ye] at hp
    exact no_977_6 q hp
  · omega

private theorem no_977_4 (q : Nat) :
    ¬ Reach (1280*q+605) (5632*q+2680) := by
  intro hr
  rcases odd_back (1280*q+605) (5632*q+2680) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 640*q+301 := by omega
    have ye : y = 6912*q+3285 := by omega
    rw [xe,ye] at hp
    exact no_977_5 q hp
  · omega

private theorem no_977_3 (q : Nat) :
    ¬ Reach (2560*q+1213) (3072*q+1467) := by
  intro hr
  rcases odd_back (2560*q+1213) (3072*q+1467) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+605 := by omega
    have ye : y = 5632*q+2680 := by omega
    rw [xe,ye] at hp
    exact no_977_4 q hp
  · omega

private theorem no_977_2 (q : Nat) :
    ¬ Reach (512*q+242) (7168*q+3417) := by
  intro hr
  have ha := reach_allowed (512*q+242) (7168*q+3417) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_977_1 (q : Nat) :
    ¬ Reach (1024*q+487) (6144*q+2930) := by
  intro hr
  rcases odd_back (1024*q+487) (6144*q+2930) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+242 := by omega
    have ye : y = 7168*q+3417 := by omega
    rw [xe,ye] at hp
    exact no_977_2 q hp
  · have xe : x = 2560*q+1213 := by omega
    have ye : y = 3072*q+1467 := by omega
    rw [xe,ye] at hp
    exact no_977_3 q hp

private theorem no_977_0 (q : Nat) :
    ¬ Reach (2048*q+977) (4096*q+1953) := by
  intro hr
  rcases odd_back (2048*q+977) (4096*q+1953) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+487 := by omega
    have ye : y = 6144*q+2930 := by omega
    rw [xe,ye] at hp
    exact no_977_1 q hp
  · omega

theorem blank_halt_not_977_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠977 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+977 := by dsimp [q]; omega
  have hb : b=4096*q+1953 := by omega
  have hr0 : Reach (2048*q+977) (4096*q+1953) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_977_0 q hr0

#print axioms blank_halt_not_977_mod2048

/-- Exact inverse-tree certificate for the all-natural 1013 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1013_6 (q : Nat) :
    ¬ Reach (2560*q+1258) (3072*q+1521) := by
  intro hr
  have ha := reach_allowed (2560*q+1258) (3072*q+1521) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1013_5 (q : Nat) :
    ¬ Reach (1088*q+533) (6016*q+2966) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_5_6 n (1088*q+533) (6016*q+2966) hn (by omega)
  omega

private theorem no_1013_4 (q : Nat) :
    ¬ Reach (2176*q+1069) (3840*q+1897) := by
  intro hr
  rcases odd_back (2176*q+1069) (3840*q+1897) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+533 := by omega
    have ye : y = 6016*q+2966 := by omega
    rw [xe,ye] at hp
    exact no_1013_5 q hp
  · omega

private theorem no_1013_3 (q : Nat) :
    ¬ Reach (256*q+124) (7680*q+3794) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+124) (7680*q+3794) (by omega) (by omega) hr
  have xe : x = 2176*q+1069 := by omega
  have ye : y = 3840*q+1897 := by omega
  rw [xe,ye] at hp
  exact no_1013_4 q hp

private theorem no_1013_2 (q : Nat) :
    ¬ Reach (512*q+251) (7168*q+3543) := by
  intro hr
  rcases odd_back (512*q+251) (7168*q+3543) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+124 := by omega
    have ye : y = 7680*q+3794 := by omega
    rw [xe,ye] at hp
    exact no_1013_3 q hp
  · omega

private theorem no_1013_1 (q : Nat) :
    ¬ Reach (1024*q+505) (6144*q+3038) := by
  intro hr
  rcases odd_back (1024*q+505) (6144*q+3038) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+251 := by omega
    have ye : y = 7168*q+3543 := by omega
    rw [xe,ye] at hp
    exact no_1013_2 q hp
  · have xe : x = 2560*q+1258 := by omega
    have ye : y = 3072*q+1521 := by omega
    rw [xe,ye] at hp
    exact no_1013_6 q hp

private theorem no_1013_0 (q : Nat) :
    ¬ Reach (2048*q+1013) (4096*q+2025) := by
  intro hr
  rcases odd_back (2048*q+1013) (4096*q+2025) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+505 := by omega
    have ye : y = 6144*q+3038 := by omega
    rw [xe,ye] at hp
    exact no_1013_1 q hp
  · omega

theorem blank_halt_not_1013_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1013 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1013 := by dsimp [q]; omega
  have hb : b=4096*q+2025 := by omega
  have hr0 : Reach (2048*q+1013) (4096*q+2025) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1013_0 q hr0

#print axioms blank_halt_not_1013_mod2048

/-- Exact inverse-tree certificate for the all-natural 1077 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1077_10 (q : Nat) :
    ¬ Reach (2560*q+1338) (3072*q+1617) := by
  intro hr
  have ha := reach_allowed (2560*q+1338) (3072*q+1617) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1077_9 (q : Nat) :
    ¬ Reach (648*q+335) (6896*q+3601) := by
  intro hr
  have ha := reach_allowed (648*q+335) (6896*q+3601) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1077_8 (q : Nat) :
    ¬ Reach (1296*q+673) (5600*q+2928) := by
  intro hr
  rcases odd_back (1296*q+673) (5600*q+2928) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 648*q+335 := by omega
    have ye : y = 6896*q+3601 := by omega
    rw [xe,ye] at hp
    exact no_1077_9 q hp
  · omega

private theorem no_1077_7 (q : Nat) :
    ¬ Reach (2592*q+1349) (3008*q+1579) := by
  intro hr
  rcases odd_back (2592*q+1349) (3008*q+1579) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1296*q+673 := by omega
    have ye : y = 5600*q+2928 := by omega
    rw [xe,ye] at hp
    exact no_1077_8 q hp
  · omega

private theorem no_1077_6 (q : Nat) :
    ¬ Reach (544*q+282) (7104*q+3721) := by
  intro hr
  have ha := reach_allowed (544*q+282) (7104*q+3721) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1077_5 (q : Nat) :
    ¬ Reach (1088*q+567) (6016*q+3154) := by
  intro hr
  rcases odd_back (1088*q+567) (6016*q+3154) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+282 := by omega
    have ye : y = 7104*q+3721 := by omega
    rw [xe,ye] at hp
    exact no_1077_6 q hp
  · have xe : x = 2592*q+1349 := by omega
    have ye : y = 3008*q+1579 := by omega
    rw [xe,ye] at hp
    exact no_1077_7 q hp

private theorem no_1077_4 (q : Nat) :
    ¬ Reach (2176*q+1137) (3840*q+2017) := by
  intro hr
  rcases odd_back (2176*q+1137) (3840*q+2017) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+567 := by omega
    have ye : y = 6016*q+3154 := by omega
    rw [xe,ye] at hp
    exact no_1077_5 q hp
  · omega

private theorem no_1077_3 (q : Nat) :
    ¬ Reach (256*q+132) (7680*q+4034) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+132) (7680*q+4034) (by omega) (by omega) hr
  have xe : x = 2176*q+1137 := by omega
  have ye : y = 3840*q+2017 := by omega
  rw [xe,ye] at hp
  exact no_1077_4 q hp

private theorem no_1077_2 (q : Nat) :
    ¬ Reach (512*q+267) (7168*q+3767) := by
  intro hr
  rcases odd_back (512*q+267) (7168*q+3767) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+132 := by omega
    have ye : y = 7680*q+4034 := by omega
    rw [xe,ye] at hp
    exact no_1077_3 q hp
  · omega

private theorem no_1077_1 (q : Nat) :
    ¬ Reach (1024*q+537) (6144*q+3230) := by
  intro hr
  rcases odd_back (1024*q+537) (6144*q+3230) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+267 := by omega
    have ye : y = 7168*q+3767 := by omega
    rw [xe,ye] at hp
    exact no_1077_2 q hp
  · have xe : x = 2560*q+1338 := by omega
    have ye : y = 3072*q+1617 := by omega
    rw [xe,ye] at hp
    exact no_1077_10 q hp

private theorem no_1077_0 (q : Nat) :
    ¬ Reach (2048*q+1077) (4096*q+2153) := by
  intro hr
  rcases odd_back (2048*q+1077) (4096*q+2153) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+537 := by omega
    have ye : y = 6144*q+3230 := by omega
    rw [xe,ye] at hp
    exact no_1077_1 q hp
  · omega

theorem blank_halt_not_1077_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1077 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1077 := by dsimp [q]; omega
  have hb : b=4096*q+2153 := by omega
  have hr0 : Reach (2048*q+1077) (4096*q+2153) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1077_0 q hr0

#print axioms blank_halt_not_1077_mod2048

end BB429AutoGroup2

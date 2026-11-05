import BB429RootMod32
import BB429NewResidue
import Lean.Elab.Tactic.Omega

namespace BB429AutoGroup1
open BB429NewResidue

set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Exact inverse-tree certificate for the all-natural 309 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_309_8 (q : Nat) :
    ¬ Reach (2560*q+378) (3072*q+465) := by
  intro hr
  have ha := reach_allowed (2560*q+378) (3072*q+465) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_309_7 (q : Nat) :
    ¬ Reach (2592*q+377) (3008*q+451) := by
  intro hr
  have ha := reach_allowed (2592*q+377) (3008*q+451) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_309_6 (q : Nat) :
    ¬ Reach (544*q+78) (7104*q+1057) := by
  intro hr
  have ha := reach_allowed (544*q+78) (7104*q+1057) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_309_5 (q : Nat) :
    ¬ Reach (1088*q+159) (6016*q+898) := by
  intro hr
  rcases odd_back (1088*q+159) (6016*q+898) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+78 := by omega
    have ye : y = 7104*q+1057 := by omega
    rw [xe,ye] at hp
    exact no_309_6 q hp
  · have xe : x = 2592*q+377 := by omega
    have ye : y = 3008*q+451 := by omega
    rw [xe,ye] at hp
    exact no_309_7 q hp

private theorem no_309_4 (q : Nat) :
    ¬ Reach (2176*q+321) (3840*q+577) := by
  intro hr
  rcases odd_back (2176*q+321) (3840*q+577) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+159 := by omega
    have ye : y = 6016*q+898 := by omega
    rw [xe,ye] at hp
    exact no_309_5 q hp
  · omega

private theorem no_309_3 (q : Nat) :
    ¬ Reach (256*q+36) (7680*q+1154) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+36) (7680*q+1154) (by omega) (by omega) hr
  have xe : x = 2176*q+321 := by omega
  have ye : y = 3840*q+577 := by omega
  rw [xe,ye] at hp
  exact no_309_4 q hp

private theorem no_309_2 (q : Nat) :
    ¬ Reach (512*q+75) (7168*q+1079) := by
  intro hr
  rcases odd_back (512*q+75) (7168*q+1079) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+36 := by omega
    have ye : y = 7680*q+1154 := by omega
    rw [xe,ye] at hp
    exact no_309_3 q hp
  · omega

private theorem no_309_1 (q : Nat) :
    ¬ Reach (1024*q+153) (6144*q+926) := by
  intro hr
  rcases odd_back (1024*q+153) (6144*q+926) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+75 := by omega
    have ye : y = 7168*q+1079 := by omega
    rw [xe,ye] at hp
    exact no_309_2 q hp
  · have xe : x = 2560*q+378 := by omega
    have ye : y = 3072*q+465 := by omega
    rw [xe,ye] at hp
    exact no_309_8 q hp

private theorem no_309_0 (q : Nat) :
    ¬ Reach (2048*q+309) (4096*q+617) := by
  intro hr
  rcases odd_back (2048*q+309) (4096*q+617) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+153 := by omega
    have ye : y = 6144*q+926 := by omega
    rw [xe,ye] at hp
    exact no_309_1 q hp
  · omega

theorem blank_halt_not_309_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠309 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+309 := by dsimp [q]; omega
  have hb : b=4096*q+617 := by omega
  have hr0 : Reach (2048*q+309) (4096*q+617) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_309_0 q hr0

#print axioms blank_halt_not_309_mod2048

/-- Exact inverse-tree certificate for the all-natural 373 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_373_6 (q : Nat) :
    ¬ Reach (2560*q+458) (3072*q+561) := by
  intro hr
  have ha := reach_allowed (2560*q+458) (3072*q+561) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_373_5 (q : Nat) :
    ¬ Reach (1088*q+193) (6016*q+1086) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_1_6 n (1088*q+193) (6016*q+1086) hn (by omega)
  omega

private theorem no_373_4 (q : Nat) :
    ¬ Reach (2176*q+389) (3840*q+697) := by
  intro hr
  rcases odd_back (2176*q+389) (3840*q+697) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+193 := by omega
    have ye : y = 6016*q+1086 := by omega
    rw [xe,ye] at hp
    exact no_373_5 q hp
  · omega

private theorem no_373_3 (q : Nat) :
    ¬ Reach (256*q+44) (7680*q+1394) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+44) (7680*q+1394) (by omega) (by omega) hr
  have xe : x = 2176*q+389 := by omega
  have ye : y = 3840*q+697 := by omega
  rw [xe,ye] at hp
  exact no_373_4 q hp

private theorem no_373_2 (q : Nat) :
    ¬ Reach (512*q+91) (7168*q+1303) := by
  intro hr
  rcases odd_back (512*q+91) (7168*q+1303) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+44 := by omega
    have ye : y = 7680*q+1394 := by omega
    rw [xe,ye] at hp
    exact no_373_3 q hp
  · omega

private theorem no_373_1 (q : Nat) :
    ¬ Reach (1024*q+185) (6144*q+1118) := by
  intro hr
  rcases odd_back (1024*q+185) (6144*q+1118) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+91 := by omega
    have ye : y = 7168*q+1303 := by omega
    rw [xe,ye] at hp
    exact no_373_2 q hp
  · have xe : x = 2560*q+458 := by omega
    have ye : y = 3072*q+561 := by omega
    rw [xe,ye] at hp
    exact no_373_6 q hp

private theorem no_373_0 (q : Nat) :
    ¬ Reach (2048*q+373) (4096*q+745) := by
  intro hr
  rcases odd_back (2048*q+373) (4096*q+745) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+185 := by omega
    have ye : y = 6144*q+1118 := by omega
    rw [xe,ye] at hp
    exact no_373_1 q hp
  · omega

theorem blank_halt_not_373_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠373 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+373 := by dsimp [q]; omega
  have hb : b=4096*q+745 := by omega
  have hr0 : Reach (2048*q+373) (4096*q+745) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_373_0 q hr0

#print axioms blank_halt_not_373_mod2048

/-- Exact inverse-tree certificate for the all-natural 437 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_437_10 (q : Nat) :
    ¬ Reach (2560*q+538) (3072*q+657) := by
  intro hr
  have ha := reach_allowed (2560*q+538) (3072*q+657) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_437_9 (q : Nat) :
    ¬ Reach (2696*q+559) (2800*q+589) := by
  intro hr
  have ha := reach_allowed (2696*q+559) (2800*q+589) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_437_8 (q : Nat) :
    ¬ Reach (1296*q+268) (5600*q+1178) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1296*q+268) (5600*q+1178) (by omega) (by omega) hr
  have xe : x = 2696*q+559 := by omega
  have ye : y = 2800*q+589 := by omega
  rw [xe,ye] at hp
  exact no_437_9 q hp

private theorem no_437_7 (q : Nat) :
    ¬ Reach (2592*q+539) (3008*q+639) := by
  intro hr
  rcases odd_back (2592*q+539) (3008*q+639) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1296*q+268 := by omega
    have ye : y = 5600*q+1178 := by omega
    rw [xe,ye] at hp
    exact no_437_8 q hp
  · omega

private theorem no_437_6 (q : Nat) :
    ¬ Reach (544*q+112) (7104*q+1501) := by
  intro hr
  have ha := reach_allowed (544*q+112) (7104*q+1501) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_437_5 (q : Nat) :
    ¬ Reach (1088*q+227) (6016*q+1274) := by
  intro hr
  rcases odd_back (1088*q+227) (6016*q+1274) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+112 := by omega
    have ye : y = 7104*q+1501 := by omega
    rw [xe,ye] at hp
    exact no_437_6 q hp
  · have xe : x = 2592*q+539 := by omega
    have ye : y = 3008*q+639 := by omega
    rw [xe,ye] at hp
    exact no_437_7 q hp

private theorem no_437_4 (q : Nat) :
    ¬ Reach (2176*q+457) (3840*q+817) := by
  intro hr
  rcases odd_back (2176*q+457) (3840*q+817) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+227 := by omega
    have ye : y = 6016*q+1274 := by omega
    rw [xe,ye] at hp
    exact no_437_5 q hp
  · omega

private theorem no_437_3 (q : Nat) :
    ¬ Reach (256*q+52) (7680*q+1634) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+52) (7680*q+1634) (by omega) (by omega) hr
  have xe : x = 2176*q+457 := by omega
  have ye : y = 3840*q+817 := by omega
  rw [xe,ye] at hp
  exact no_437_4 q hp

private theorem no_437_2 (q : Nat) :
    ¬ Reach (512*q+107) (7168*q+1527) := by
  intro hr
  rcases odd_back (512*q+107) (7168*q+1527) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+52 := by omega
    have ye : y = 7680*q+1634 := by omega
    rw [xe,ye] at hp
    exact no_437_3 q hp
  · omega

private theorem no_437_1 (q : Nat) :
    ¬ Reach (1024*q+217) (6144*q+1310) := by
  intro hr
  rcases odd_back (1024*q+217) (6144*q+1310) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+107 := by omega
    have ye : y = 7168*q+1527 := by omega
    rw [xe,ye] at hp
    exact no_437_2 q hp
  · have xe : x = 2560*q+538 := by omega
    have ye : y = 3072*q+657 := by omega
    rw [xe,ye] at hp
    exact no_437_10 q hp

private theorem no_437_0 (q : Nat) :
    ¬ Reach (2048*q+437) (4096*q+873) := by
  intro hr
  rcases odd_back (2048*q+437) (4096*q+873) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+217 := by omega
    have ye : y = 6144*q+1310 := by omega
    rw [xe,ye] at hp
    exact no_437_1 q hp
  · omega

theorem blank_halt_not_437_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠437 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+437 := by dsimp [q]; omega
  have hb : b=4096*q+873 := by omega
  have hr0 : Reach (2048*q+437) (4096*q+873) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_437_0 q hr0

#print axioms blank_halt_not_437_mod2048

/-- Exact inverse-tree certificate for the all-natural 457 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_457_6 (q : Nat) :
    ¬ Reach (1344*q+293) (5504*q+1214) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_5_6 n (1344*q+293) (5504*q+1214) hn (by omega)
  omega

private theorem no_457_5 (q : Nat) :
    ¬ Reach (2688*q+589) (2816*q+625) := by
  intro hr
  rcases odd_back (2688*q+589) (2816*q+625) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+293 := by omega
    have ye : y = 5504*q+1214 := by omega
    rw [xe,ye] at hp
    exact no_457_6 q hp
  · omega

private theorem no_457_4 (q : Nat) :
    ¬ Reach (1280*q+280) (5632*q+1250) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+280) (5632*q+1250) (by omega) (by omega) hr
  have xe : x = 2688*q+589 := by omega
  have ye : y = 2816*q+625 := by omega
  rw [xe,ye] at hp
  exact no_457_5 q hp

private theorem no_457_3 (q : Nat) :
    ¬ Reach (2560*q+563) (3072*q+687) := by
  intro hr
  rcases odd_back (2560*q+563) (3072*q+687) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+280 := by omega
    have ye : y = 5632*q+1250 := by omega
    rw [xe,ye] at hp
    exact no_457_4 q hp
  · omega

private theorem no_457_2 (q : Nat) :
    ¬ Reach (512*q+112) (7168*q+1597) := by
  intro hr
  have ha := reach_allowed (512*q+112) (7168*q+1597) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_457_1 (q : Nat) :
    ¬ Reach (1024*q+227) (6144*q+1370) := by
  intro hr
  rcases odd_back (1024*q+227) (6144*q+1370) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+112 := by omega
    have ye : y = 7168*q+1597 := by omega
    rw [xe,ye] at hp
    exact no_457_2 q hp
  · have xe : x = 2560*q+563 := by omega
    have ye : y = 3072*q+687 := by omega
    rw [xe,ye] at hp
    exact no_457_3 q hp

private theorem no_457_0 (q : Nat) :
    ¬ Reach (2048*q+457) (4096*q+913) := by
  intro hr
  rcases odd_back (2048*q+457) (4096*q+913) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+227 := by omega
    have ye : y = 6144*q+1370 := by omega
    rw [xe,ye] at hp
    exact no_457_1 q hp
  · omega

theorem blank_halt_not_457_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠457 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+457 := by dsimp [q]; omega
  have hb : b=4096*q+913 := by omega
  have hr0 : Reach (2048*q+457) (4096*q+913) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_457_0 q hr0

#print axioms blank_halt_not_457_mod2048

/-- Exact inverse-tree certificate for the all-natural 501 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_501_6 (q : Nat) :
    ¬ Reach (2560*q+618) (3072*q+753) := by
  intro hr
  have ha := reach_allowed (2560*q+618) (3072*q+753) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_501_5 (q : Nat) :
    ¬ Reach (1088*q+261) (6016*q+1462) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_5_6 n (1088*q+261) (6016*q+1462) hn (by omega)
  omega

private theorem no_501_4 (q : Nat) :
    ¬ Reach (2176*q+525) (3840*q+937) := by
  intro hr
  rcases odd_back (2176*q+525) (3840*q+937) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+261 := by omega
    have ye : y = 6016*q+1462 := by omega
    rw [xe,ye] at hp
    exact no_501_5 q hp
  · omega

private theorem no_501_3 (q : Nat) :
    ¬ Reach (256*q+60) (7680*q+1874) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+60) (7680*q+1874) (by omega) (by omega) hr
  have xe : x = 2176*q+525 := by omega
  have ye : y = 3840*q+937 := by omega
  rw [xe,ye] at hp
  exact no_501_4 q hp

private theorem no_501_2 (q : Nat) :
    ¬ Reach (512*q+123) (7168*q+1751) := by
  intro hr
  rcases odd_back (512*q+123) (7168*q+1751) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+60 := by omega
    have ye : y = 7680*q+1874 := by omega
    rw [xe,ye] at hp
    exact no_501_3 q hp
  · omega

private theorem no_501_1 (q : Nat) :
    ¬ Reach (1024*q+249) (6144*q+1502) := by
  intro hr
  rcases odd_back (1024*q+249) (6144*q+1502) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+123 := by omega
    have ye : y = 7168*q+1751 := by omega
    rw [xe,ye] at hp
    exact no_501_2 q hp
  · have xe : x = 2560*q+618 := by omega
    have ye : y = 3072*q+753 := by omega
    rw [xe,ye] at hp
    exact no_501_6 q hp

private theorem no_501_0 (q : Nat) :
    ¬ Reach (2048*q+501) (4096*q+1001) := by
  intro hr
  rcases odd_back (2048*q+501) (4096*q+1001) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+249 := by omega
    have ye : y = 6144*q+1502 := by omega
    rw [xe,ye] at hp
    exact no_501_1 q hp
  · omega

theorem blank_halt_not_501_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠501 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+501 := by dsimp [q]; omega
  have hb : b=4096*q+1001 := by omega
  have hr0 : Reach (2048*q+501) (4096*q+1001) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_501_0 q hr0

#print axioms blank_halt_not_501_mod2048

/-- Exact inverse-tree certificate for the all-natural 593 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_593_9 (q : Nat) :
    ¬ Reach (2208*q+625) (3776*q+1087) := by
  intro hr
  have ha := reach_allowed (2208*q+625) (3776*q+1087) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_593_8 (q : Nat) :
    ¬ Reach (80*q+20) (8032*q+2302) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (80*q+20) (8032*q+2302) hn (by omega) (by omega)
  omega

private theorem no_593_7 (q : Nat) :
    ¬ Reach (160*q+43) (7872*q+2259) := by
  intro hr
  rcases odd_back (160*q+43) (7872*q+2259) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 80*q+20 := by omega
    have ye : y = 8032*q+2302 := by omega
    rw [xe,ye] at hp
    exact no_593_8 q hp
  · omega

private theorem no_593_6 (q : Nat) :
    ¬ Reach (320*q+89) (7552*q+2170) := by
  intro hr
  rcases odd_back (320*q+89) (7552*q+2170) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 160*q+43 := by omega
    have ye : y = 7872*q+2259 := by omega
    rw [xe,ye] at hp
    exact no_593_7 q hp
  · have xe : x = 2208*q+625 := by omega
    have ye : y = 3776*q+1087 := by omega
    rw [xe,ye] at hp
    exact no_593_9 q hp

private theorem no_593_5 (q : Nat) :
    ¬ Reach (640*q+181) (6912*q+1989) := by
  intro hr
  rcases odd_back (640*q+181) (6912*q+1989) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 320*q+89 := by omega
    have ye : y = 7552*q+2170 := by omega
    rw [xe,ye] at hp
    exact no_593_6 q hp
  · omega

private theorem no_593_4 (q : Nat) :
    ¬ Reach (1280*q+365) (5632*q+1624) := by
  intro hr
  rcases odd_back (1280*q+365) (5632*q+1624) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 640*q+181 := by omega
    have ye : y = 6912*q+1989 := by omega
    rw [xe,ye] at hp
    exact no_593_5 q hp
  · omega

private theorem no_593_3 (q : Nat) :
    ¬ Reach (2560*q+733) (3072*q+891) := by
  intro hr
  rcases odd_back (2560*q+733) (3072*q+891) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+365 := by omega
    have ye : y = 5632*q+1624 := by omega
    rw [xe,ye] at hp
    exact no_593_4 q hp
  · omega

private theorem no_593_2 (q : Nat) :
    ¬ Reach (512*q+146) (7168*q+2073) := by
  intro hr
  have ha := reach_allowed (512*q+146) (7168*q+2073) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_593_1 (q : Nat) :
    ¬ Reach (1024*q+295) (6144*q+1778) := by
  intro hr
  rcases odd_back (1024*q+295) (6144*q+1778) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+146 := by omega
    have ye : y = 7168*q+2073 := by omega
    rw [xe,ye] at hp
    exact no_593_2 q hp
  · have xe : x = 2560*q+733 := by omega
    have ye : y = 3072*q+891 := by omega
    rw [xe,ye] at hp
    exact no_593_3 q hp

private theorem no_593_0 (q : Nat) :
    ¬ Reach (2048*q+593) (4096*q+1185) := by
  intro hr
  rcases odd_back (2048*q+593) (4096*q+1185) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+295 := by omega
    have ye : y = 6144*q+1778 := by omega
    rw [xe,ye] at hp
    exact no_593_1 q hp
  · omega

theorem blank_halt_not_593_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠593 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+593 := by dsimp [q]; omega
  have hb : b=4096*q+1185 := by omega
  have hr0 : Reach (2048*q+593) (4096*q+1185) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_593_0 q hr0

#print axioms blank_halt_not_593_mod2048

/-- Exact inverse-tree certificate for the all-natural 693 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_693_8 (q : Nat) :
    ¬ Reach (2560*q+858) (3072*q+1041) := by
  intro hr
  have ha := reach_allowed (2560*q+858) (3072*q+1041) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_693_7 (q : Nat) :
    ¬ Reach (2592*q+863) (3008*q+1015) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_7_7 n (2592*q+863) (3008*q+1015) hn (by omega)
  omega

private theorem no_693_6 (q : Nat) :
    ¬ Reach (544*q+180) (7104*q+2389) := by
  intro hr
  have ha := reach_allowed (544*q+180) (7104*q+2389) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_693_5 (q : Nat) :
    ¬ Reach (1088*q+363) (6016*q+2026) := by
  intro hr
  rcases odd_back (1088*q+363) (6016*q+2026) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+180 := by omega
    have ye : y = 7104*q+2389 := by omega
    rw [xe,ye] at hp
    exact no_693_6 q hp
  · have xe : x = 2592*q+863 := by omega
    have ye : y = 3008*q+1015 := by omega
    rw [xe,ye] at hp
    exact no_693_7 q hp

private theorem no_693_4 (q : Nat) :
    ¬ Reach (2176*q+729) (3840*q+1297) := by
  intro hr
  rcases odd_back (2176*q+729) (3840*q+1297) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+363 := by omega
    have ye : y = 6016*q+2026 := by omega
    rw [xe,ye] at hp
    exact no_693_5 q hp
  · omega

private theorem no_693_3 (q : Nat) :
    ¬ Reach (256*q+84) (7680*q+2594) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+84) (7680*q+2594) (by omega) (by omega) hr
  have xe : x = 2176*q+729 := by omega
  have ye : y = 3840*q+1297 := by omega
  rw [xe,ye] at hp
  exact no_693_4 q hp

private theorem no_693_2 (q : Nat) :
    ¬ Reach (512*q+171) (7168*q+2423) := by
  intro hr
  rcases odd_back (512*q+171) (7168*q+2423) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+84 := by omega
    have ye : y = 7680*q+2594 := by omega
    rw [xe,ye] at hp
    exact no_693_3 q hp
  · omega

private theorem no_693_1 (q : Nat) :
    ¬ Reach (1024*q+345) (6144*q+2078) := by
  intro hr
  rcases odd_back (1024*q+345) (6144*q+2078) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+171 := by omega
    have ye : y = 7168*q+2423 := by omega
    rw [xe,ye] at hp
    exact no_693_2 q hp
  · have xe : x = 2560*q+858 := by omega
    have ye : y = 3072*q+1041 := by omega
    rw [xe,ye] at hp
    exact no_693_8 q hp

private theorem no_693_0 (q : Nat) :
    ¬ Reach (2048*q+693) (4096*q+1385) := by
  intro hr
  rcases odd_back (2048*q+693) (4096*q+1385) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+345 := by omega
    have ye : y = 6144*q+2078 := by omega
    rw [xe,ye] at hp
    exact no_693_1 q hp
  · omega

theorem blank_halt_not_693_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠693 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+693 := by dsimp [q]; omega
  have hb : b=4096*q+1385 := by omega
  have hr0 : Reach (2048*q+693) (4096*q+1385) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_693_0 q hr0

#print axioms blank_halt_not_693_mod2048

/-- Exact inverse-tree certificate for the all-natural 713 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_713_10 (q : Nat) :
    ¬ Reach (2720*q+930) (2752*q+953) := by
  intro hr
  have ha := reach_allowed (2720*q+930) (2752*q+953) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_713_9 (q : Nat) :
    ¬ Reach (168*q+55) (7856*q+2705) := by
  intro hr
  have ha := reach_allowed (168*q+55) (7856*q+2705) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_713_8 (q : Nat) :
    ¬ Reach (336*q+113) (7520*q+2592) := by
  intro hr
  rcases odd_back (336*q+113) (7520*q+2592) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 168*q+55 := by omega
    have ye : y = 7856*q+2705 := by omega
    rw [xe,ye] at hp
    exact no_713_9 q hp
  · omega

private theorem no_713_7 (q : Nat) :
    ¬ Reach (672*q+229) (6848*q+2363) := by
  intro hr
  rcases odd_back (672*q+229) (6848*q+2363) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 336*q+113 := by omega
    have ye : y = 7520*q+2592 := by omega
    rw [xe,ye] at hp
    exact no_713_8 q hp
  · omega

private theorem no_713_6 (q : Nat) :
    ¬ Reach (1344*q+461) (5504*q+1902) := by
  intro hr
  rcases odd_back (1344*q+461) (5504*q+1902) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 672*q+229 := by omega
    have ye : y = 6848*q+2363 := by omega
    rw [xe,ye] at hp
    exact no_713_7 q hp
  · have xe : x = 2720*q+930 := by omega
    have ye : y = 2752*q+953 := by omega
    rw [xe,ye] at hp
    exact no_713_10 q hp

private theorem no_713_5 (q : Nat) :
    ¬ Reach (2688*q+925) (2816*q+977) := by
  intro hr
  rcases odd_back (2688*q+925) (2816*q+977) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+461 := by omega
    have ye : y = 5504*q+1902 := by omega
    rw [xe,ye] at hp
    exact no_713_6 q hp
  · omega

private theorem no_713_4 (q : Nat) :
    ¬ Reach (1280*q+440) (5632*q+1954) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+440) (5632*q+1954) (by omega) (by omega) hr
  have xe : x = 2688*q+925 := by omega
  have ye : y = 2816*q+977 := by omega
  rw [xe,ye] at hp
  exact no_713_5 q hp

private theorem no_713_3 (q : Nat) :
    ¬ Reach (2560*q+883) (3072*q+1071) := by
  intro hr
  rcases odd_back (2560*q+883) (3072*q+1071) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+440 := by omega
    have ye : y = 5632*q+1954 := by omega
    rw [xe,ye] at hp
    exact no_713_4 q hp
  · omega

private theorem no_713_2 (q : Nat) :
    ¬ Reach (512*q+176) (7168*q+2493) := by
  intro hr
  have ha := reach_allowed (512*q+176) (7168*q+2493) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_713_1 (q : Nat) :
    ¬ Reach (1024*q+355) (6144*q+2138) := by
  intro hr
  rcases odd_back (1024*q+355) (6144*q+2138) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+176 := by omega
    have ye : y = 7168*q+2493 := by omega
    rw [xe,ye] at hp
    exact no_713_2 q hp
  · have xe : x = 2560*q+883 := by omega
    have ye : y = 3072*q+1071 := by omega
    rw [xe,ye] at hp
    exact no_713_3 q hp

private theorem no_713_0 (q : Nat) :
    ¬ Reach (2048*q+713) (4096*q+1425) := by
  intro hr
  rcases odd_back (2048*q+713) (4096*q+1425) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+355 := by omega
    have ye : y = 6144*q+2138 := by omega
    rw [xe,ye] at hp
    exact no_713_1 q hp
  · omega

theorem blank_halt_not_713_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠713 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+713 := by dsimp [q]; omega
  have hb : b=4096*q+1425 := by omega
  have hr0 : Reach (2048*q+713) (4096*q+1425) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_713_0 q hr0

#print axioms blank_halt_not_713_mod2048

end BB429AutoGroup1

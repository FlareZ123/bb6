import BB429RootMod32
import BB429NewResidue
import Lean.Elab.Tactic.Omega

namespace BB429AutoGroup3
open BB429NewResidue

set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Exact inverse-tree certificate for the all-natural 1105 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1105_9 (q : Nat) :
    ¬ Reach (2208*q+1177) (3776*q+2031) := by
  intro hr
  have ha := reach_allowed (2208*q+1177) (3776*q+2031) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1105_8 (q : Nat) :
    ¬ Reach (80*q+40) (8032*q+4310) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootEven8.rooted_positive_even_eight n (80*q+40) (8032*q+4310) hn (by omega) (by omega)
  omega

private theorem no_1105_7 (q : Nat) :
    ¬ Reach (160*q+83) (7872*q+4227) := by
  intro hr
  rcases odd_back (160*q+83) (7872*q+4227) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 80*q+40 := by omega
    have ye : y = 8032*q+4310 := by omega
    rw [xe,ye] at hp
    exact no_1105_8 q hp
  · omega

private theorem no_1105_6 (q : Nat) :
    ¬ Reach (320*q+169) (7552*q+4058) := by
  intro hr
  rcases odd_back (320*q+169) (7552*q+4058) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 160*q+83 := by omega
    have ye : y = 7872*q+4227 := by omega
    rw [xe,ye] at hp
    exact no_1105_7 q hp
  · have xe : x = 2208*q+1177 := by omega
    have ye : y = 3776*q+2031 := by omega
    rw [xe,ye] at hp
    exact no_1105_9 q hp

private theorem no_1105_5 (q : Nat) :
    ¬ Reach (640*q+341) (6912*q+3717) := by
  intro hr
  rcases odd_back (640*q+341) (6912*q+3717) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 320*q+169 := by omega
    have ye : y = 7552*q+4058 := by omega
    rw [xe,ye] at hp
    exact no_1105_6 q hp
  · omega

private theorem no_1105_4 (q : Nat) :
    ¬ Reach (1280*q+685) (5632*q+3032) := by
  intro hr
  rcases odd_back (1280*q+685) (5632*q+3032) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 640*q+341 := by omega
    have ye : y = 6912*q+3717 := by omega
    rw [xe,ye] at hp
    exact no_1105_5 q hp
  · omega

private theorem no_1105_3 (q : Nat) :
    ¬ Reach (2560*q+1373) (3072*q+1659) := by
  intro hr
  rcases odd_back (2560*q+1373) (3072*q+1659) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+685 := by omega
    have ye : y = 5632*q+3032 := by omega
    rw [xe,ye] at hp
    exact no_1105_4 q hp
  · omega

private theorem no_1105_2 (q : Nat) :
    ¬ Reach (512*q+274) (7168*q+3865) := by
  intro hr
  have ha := reach_allowed (512*q+274) (7168*q+3865) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1105_1 (q : Nat) :
    ¬ Reach (1024*q+551) (6144*q+3314) := by
  intro hr
  rcases odd_back (1024*q+551) (6144*q+3314) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+274 := by omega
    have ye : y = 7168*q+3865 := by omega
    rw [xe,ye] at hp
    exact no_1105_2 q hp
  · have xe : x = 2560*q+1373 := by omega
    have ye : y = 3072*q+1659 := by omega
    rw [xe,ye] at hp
    exact no_1105_3 q hp

private theorem no_1105_0 (q : Nat) :
    ¬ Reach (2048*q+1105) (4096*q+2209) := by
  intro hr
  rcases odd_back (2048*q+1105) (4096*q+2209) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+551 := by omega
    have ye : y = 6144*q+3314 := by omega
    rw [xe,ye] at hp
    exact no_1105_1 q hp
  · omega

theorem blank_halt_not_1105_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1105 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1105 := by dsimp [q]; omega
  have hb : b=4096*q+2209 := by omega
  have hr0 : Reach (2048*q+1105) (4096*q+2209) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1105_0 q hr0

#print axioms blank_halt_not_1105_mod2048

/-- Exact inverse-tree certificate for the all-natural 1205 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1205_8 (q : Nat) :
    ¬ Reach (2560*q+1498) (3072*q+1809) := by
  intro hr
  have ha := reach_allowed (2560*q+1498) (3072*q+1809) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1205_7 (q : Nat) :
    ¬ Reach (2592*q+1511) (3008*q+1767) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_7_7 n (2592*q+1511) (3008*q+1767) hn (by omega)
  omega

private theorem no_1205_6 (q : Nat) :
    ¬ Reach (544*q+316) (7104*q+4165) := by
  intro hr
  have ha := reach_allowed (544*q+316) (7104*q+4165) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1205_5 (q : Nat) :
    ¬ Reach (1088*q+635) (6016*q+3530) := by
  intro hr
  rcases odd_back (1088*q+635) (6016*q+3530) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+316 := by omega
    have ye : y = 7104*q+4165 := by omega
    rw [xe,ye] at hp
    exact no_1205_6 q hp
  · have xe : x = 2592*q+1511 := by omega
    have ye : y = 3008*q+1767 := by omega
    rw [xe,ye] at hp
    exact no_1205_7 q hp

private theorem no_1205_4 (q : Nat) :
    ¬ Reach (2176*q+1273) (3840*q+2257) := by
  intro hr
  rcases odd_back (2176*q+1273) (3840*q+2257) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+635 := by omega
    have ye : y = 6016*q+3530 := by omega
    rw [xe,ye] at hp
    exact no_1205_5 q hp
  · omega

private theorem no_1205_3 (q : Nat) :
    ¬ Reach (256*q+148) (7680*q+4514) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+148) (7680*q+4514) (by omega) (by omega) hr
  have xe : x = 2176*q+1273 := by omega
  have ye : y = 3840*q+2257 := by omega
  rw [xe,ye] at hp
  exact no_1205_4 q hp

private theorem no_1205_2 (q : Nat) :
    ¬ Reach (512*q+299) (7168*q+4215) := by
  intro hr
  rcases odd_back (512*q+299) (7168*q+4215) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+148 := by omega
    have ye : y = 7680*q+4514 := by omega
    rw [xe,ye] at hp
    exact no_1205_3 q hp
  · omega

private theorem no_1205_1 (q : Nat) :
    ¬ Reach (1024*q+601) (6144*q+3614) := by
  intro hr
  rcases odd_back (1024*q+601) (6144*q+3614) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+299 := by omega
    have ye : y = 7168*q+4215 := by omega
    rw [xe,ye] at hp
    exact no_1205_2 q hp
  · have xe : x = 2560*q+1498 := by omega
    have ye : y = 3072*q+1809 := by omega
    rw [xe,ye] at hp
    exact no_1205_8 q hp

private theorem no_1205_0 (q : Nat) :
    ¬ Reach (2048*q+1205) (4096*q+2409) := by
  intro hr
  rcases odd_back (2048*q+1205) (4096*q+2409) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+601 := by omega
    have ye : y = 6144*q+3614 := by omega
    rw [xe,ye] at hp
    exact no_1205_1 q hp
  · omega

theorem blank_halt_not_1205_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1205 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1205 := by dsimp [q]; omega
  have hb : b=4096*q+2409 := by omega
  have hr0 : Reach (2048*q+1205) (4096*q+2409) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1205_0 q hr0

#print axioms blank_halt_not_1205_mod2048

/-- Exact inverse-tree certificate for the all-natural 1333 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1333_8 (q : Nat) :
    ¬ Reach (2560*q+1658) (3072*q+2001) := by
  intro hr
  have ha := reach_allowed (2560*q+1658) (3072*q+2001) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1333_7 (q : Nat) :
    ¬ Reach (2592*q+1673) (3008*q+1955) := by
  intro hr
  have ha := reach_allowed (2592*q+1673) (3008*q+1955) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1333_6 (q : Nat) :
    ¬ Reach (544*q+350) (7104*q+4609) := by
  intro hr
  have ha := reach_allowed (544*q+350) (7104*q+4609) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1333_5 (q : Nat) :
    ¬ Reach (1088*q+703) (6016*q+3906) := by
  intro hr
  rcases odd_back (1088*q+703) (6016*q+3906) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 544*q+350 := by omega
    have ye : y = 7104*q+4609 := by omega
    rw [xe,ye] at hp
    exact no_1333_6 q hp
  · have xe : x = 2592*q+1673 := by omega
    have ye : y = 3008*q+1955 := by omega
    rw [xe,ye] at hp
    exact no_1333_7 q hp

private theorem no_1333_4 (q : Nat) :
    ¬ Reach (2176*q+1409) (3840*q+2497) := by
  intro hr
  rcases odd_back (2176*q+1409) (3840*q+2497) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+703 := by omega
    have ye : y = 6016*q+3906 := by omega
    rw [xe,ye] at hp
    exact no_1333_5 q hp
  · omega

private theorem no_1333_3 (q : Nat) :
    ¬ Reach (256*q+164) (7680*q+4994) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+164) (7680*q+4994) (by omega) (by omega) hr
  have xe : x = 2176*q+1409 := by omega
  have ye : y = 3840*q+2497 := by omega
  rw [xe,ye] at hp
  exact no_1333_4 q hp

private theorem no_1333_2 (q : Nat) :
    ¬ Reach (512*q+331) (7168*q+4663) := by
  intro hr
  rcases odd_back (512*q+331) (7168*q+4663) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+164 := by omega
    have ye : y = 7680*q+4994 := by omega
    rw [xe,ye] at hp
    exact no_1333_3 q hp
  · omega

private theorem no_1333_1 (q : Nat) :
    ¬ Reach (1024*q+665) (6144*q+3998) := by
  intro hr
  rcases odd_back (1024*q+665) (6144*q+3998) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+331 := by omega
    have ye : y = 7168*q+4663 := by omega
    rw [xe,ye] at hp
    exact no_1333_2 q hp
  · have xe : x = 2560*q+1658 := by omega
    have ye : y = 3072*q+2001 := by omega
    rw [xe,ye] at hp
    exact no_1333_8 q hp

private theorem no_1333_0 (q : Nat) :
    ¬ Reach (2048*q+1333) (4096*q+2665) := by
  intro hr
  rcases odd_back (2048*q+1333) (4096*q+2665) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+665 := by omega
    have ye : y = 6144*q+3998 := by omega
    rw [xe,ye] at hp
    exact no_1333_1 q hp
  · omega

theorem blank_halt_not_1333_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1333 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1333 := by dsimp [q]; omega
  have hb : b=4096*q+2665 := by omega
  have hr0 : Reach (2048*q+1333) (4096*q+2665) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1333_0 q hr0

#print axioms blank_halt_not_1333_mod2048

/-- Exact inverse-tree certificate for the all-natural 1353 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1353_5 (q : Nat) :
    ¬ Reach (2688*q+1765) (2816*q+1857) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod32.rooted_not_5_1 n (2688*q+1765) (2816*q+1857) hn (by omega)
  omega

private theorem no_1353_4 (q : Nat) :
    ¬ Reach (1280*q+840) (5632*q+3714) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+840) (5632*q+3714) (by omega) (by omega) hr
  have xe : x = 2688*q+1765 := by omega
  have ye : y = 2816*q+1857 := by omega
  rw [xe,ye] at hp
  exact no_1353_5 q hp

private theorem no_1353_3 (q : Nat) :
    ¬ Reach (2560*q+1683) (3072*q+2031) := by
  intro hr
  rcases odd_back (2560*q+1683) (3072*q+2031) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+840 := by omega
    have ye : y = 5632*q+3714 := by omega
    rw [xe,ye] at hp
    exact no_1353_4 q hp
  · omega

private theorem no_1353_2 (q : Nat) :
    ¬ Reach (512*q+336) (7168*q+4733) := by
  intro hr
  have ha := reach_allowed (512*q+336) (7168*q+4733) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1353_1 (q : Nat) :
    ¬ Reach (1024*q+675) (6144*q+4058) := by
  intro hr
  rcases odd_back (1024*q+675) (6144*q+4058) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+336 := by omega
    have ye : y = 7168*q+4733 := by omega
    rw [xe,ye] at hp
    exact no_1353_2 q hp
  · have xe : x = 2560*q+1683 := by omega
    have ye : y = 3072*q+2031 := by omega
    rw [xe,ye] at hp
    exact no_1353_3 q hp

private theorem no_1353_0 (q : Nat) :
    ¬ Reach (2048*q+1353) (4096*q+2705) := by
  intro hr
  rcases odd_back (2048*q+1353) (4096*q+2705) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+675 := by omega
    have ye : y = 6144*q+4058 := by omega
    rw [xe,ye] at hp
    exact no_1353_1 q hp
  · omega

theorem blank_halt_not_1353_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1353 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1353 := by dsimp [q]; omega
  have hb : b=4096*q+2705 := by omega
  have hr0 : Reach (2048*q+1353) (4096*q+2705) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1353_0 q hr0

#print axioms blank_halt_not_1353_mod2048

/-- Exact inverse-tree certificate for the all-natural 1397 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1397_6 (q : Nat) :
    ¬ Reach (2560*q+1738) (3072*q+2097) := by
  intro hr
  have ha := reach_allowed (2560*q+1738) (3072*q+2097) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1397_5 (q : Nat) :
    ¬ Reach (1088*q+737) (6016*q+4094) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_1_6 n (1088*q+737) (6016*q+4094) hn (by omega)
  omega

private theorem no_1397_4 (q : Nat) :
    ¬ Reach (2176*q+1477) (3840*q+2617) := by
  intro hr
  rcases odd_back (2176*q+1477) (3840*q+2617) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+737 := by omega
    have ye : y = 6016*q+4094 := by omega
    rw [xe,ye] at hp
    exact no_1397_5 q hp
  · omega

private theorem no_1397_3 (q : Nat) :
    ¬ Reach (256*q+172) (7680*q+5234) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+172) (7680*q+5234) (by omega) (by omega) hr
  have xe : x = 2176*q+1477 := by omega
  have ye : y = 3840*q+2617 := by omega
  rw [xe,ye] at hp
  exact no_1397_4 q hp

private theorem no_1397_2 (q : Nat) :
    ¬ Reach (512*q+347) (7168*q+4887) := by
  intro hr
  rcases odd_back (512*q+347) (7168*q+4887) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+172 := by omega
    have ye : y = 7680*q+5234 := by omega
    rw [xe,ye] at hp
    exact no_1397_3 q hp
  · omega

private theorem no_1397_1 (q : Nat) :
    ¬ Reach (1024*q+697) (6144*q+4190) := by
  intro hr
  rcases odd_back (1024*q+697) (6144*q+4190) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+347 := by omega
    have ye : y = 7168*q+4887 := by omega
    rw [xe,ye] at hp
    exact no_1397_2 q hp
  · have xe : x = 2560*q+1738 := by omega
    have ye : y = 3072*q+2097 := by omega
    rw [xe,ye] at hp
    exact no_1397_6 q hp

private theorem no_1397_0 (q : Nat) :
    ¬ Reach (2048*q+1397) (4096*q+2793) := by
  intro hr
  rcases odd_back (2048*q+1397) (4096*q+2793) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+697 := by omega
    have ye : y = 6144*q+4190 := by omega
    rw [xe,ye] at hp
    exact no_1397_1 q hp
  · omega

theorem blank_halt_not_1397_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1397 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1397 := by dsimp [q]; omega
  have hb : b=4096*q+2793 := by omega
  have hr0 : Reach (2048*q+1397) (4096*q+2793) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1397_0 q hr0

#print axioms blank_halt_not_1397_mod2048

/-- Exact inverse-tree certificate for the all-natural 1481 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1481_6 (q : Nat) :
    ¬ Reach (1344*q+965) (5504*q+3966) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_5_6 n (1344*q+965) (5504*q+3966) hn (by omega)
  omega

private theorem no_1481_5 (q : Nat) :
    ¬ Reach (2688*q+1933) (2816*q+2033) := by
  intro hr
  rcases odd_back (2688*q+1933) (2816*q+2033) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+965 := by omega
    have ye : y = 5504*q+3966 := by omega
    rw [xe,ye] at hp
    exact no_1481_6 q hp
  · omega

private theorem no_1481_4 (q : Nat) :
    ¬ Reach (1280*q+920) (5632*q+4066) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+920) (5632*q+4066) (by omega) (by omega) hr
  have xe : x = 2688*q+1933 := by omega
  have ye : y = 2816*q+2033 := by omega
  rw [xe,ye] at hp
  exact no_1481_5 q hp

private theorem no_1481_3 (q : Nat) :
    ¬ Reach (2560*q+1843) (3072*q+2223) := by
  intro hr
  rcases odd_back (2560*q+1843) (3072*q+2223) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+920 := by omega
    have ye : y = 5632*q+4066 := by omega
    rw [xe,ye] at hp
    exact no_1481_4 q hp
  · omega

private theorem no_1481_2 (q : Nat) :
    ¬ Reach (512*q+368) (7168*q+5181) := by
  intro hr
  have ha := reach_allowed (512*q+368) (7168*q+5181) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1481_1 (q : Nat) :
    ¬ Reach (1024*q+739) (6144*q+4442) := by
  intro hr
  rcases odd_back (1024*q+739) (6144*q+4442) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+368 := by omega
    have ye : y = 7168*q+5181 := by omega
    rw [xe,ye] at hp
    exact no_1481_2 q hp
  · have xe : x = 2560*q+1843 := by omega
    have ye : y = 3072*q+2223 := by omega
    rw [xe,ye] at hp
    exact no_1481_3 q hp

private theorem no_1481_0 (q : Nat) :
    ¬ Reach (2048*q+1481) (4096*q+2961) := by
  intro hr
  rcases odd_back (2048*q+1481) (4096*q+2961) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+739 := by omega
    have ye : y = 6144*q+4442 := by omega
    rw [xe,ye] at hp
    exact no_1481_1 q hp
  · omega

theorem blank_halt_not_1481_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1481 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1481 := by dsimp [q]; omega
  have hb : b=4096*q+2961 := by omega
  have hr0 : Reach (2048*q+1481) (4096*q+2961) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1481_0 q hr0

#print axioms blank_halt_not_1481_mod2048

/-- Exact inverse-tree certificate for the all-natural 1525 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1525_6 (q : Nat) :
    ¬ Reach (2560*q+1898) (3072*q+2289) := by
  intro hr
  have ha := reach_allowed (2560*q+1898) (3072*q+2289) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1525_5 (q : Nat) :
    ¬ Reach (1088*q+805) (6016*q+4470) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod16.rooted_not_5_6 n (1088*q+805) (6016*q+4470) hn (by omega)
  omega

private theorem no_1525_4 (q : Nat) :
    ¬ Reach (2176*q+1613) (3840*q+2857) := by
  intro hr
  rcases odd_back (2176*q+1613) (3840*q+2857) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1088*q+805 := by omega
    have ye : y = 6016*q+4470 := by omega
    rw [xe,ye] at hp
    exact no_1525_5 q hp
  · omega

private theorem no_1525_3 (q : Nat) :
    ¬ Reach (256*q+188) (7680*q+5714) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (256*q+188) (7680*q+5714) (by omega) (by omega) hr
  have xe : x = 2176*q+1613 := by omega
  have ye : y = 3840*q+2857 := by omega
  rw [xe,ye] at hp
  exact no_1525_4 q hp

private theorem no_1525_2 (q : Nat) :
    ¬ Reach (512*q+379) (7168*q+5335) := by
  intro hr
  rcases odd_back (512*q+379) (7168*q+5335) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 256*q+188 := by omega
    have ye : y = 7680*q+5714 := by omega
    rw [xe,ye] at hp
    exact no_1525_3 q hp
  · omega

private theorem no_1525_1 (q : Nat) :
    ¬ Reach (1024*q+761) (6144*q+4574) := by
  intro hr
  rcases odd_back (1024*q+761) (6144*q+4574) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+379 := by omega
    have ye : y = 7168*q+5335 := by omega
    rw [xe,ye] at hp
    exact no_1525_2 q hp
  · have xe : x = 2560*q+1898 := by omega
    have ye : y = 3072*q+2289 := by omega
    rw [xe,ye] at hp
    exact no_1525_6 q hp

private theorem no_1525_0 (q : Nat) :
    ¬ Reach (2048*q+1525) (4096*q+3049) := by
  intro hr
  rcases odd_back (2048*q+1525) (4096*q+3049) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+761 := by omega
    have ye : y = 6144*q+4574 := by omega
    rw [xe,ye] at hp
    exact no_1525_1 q hp
  · omega

theorem blank_halt_not_1525_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1525 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1525 := by dsimp [q]; omega
  have hb : b=4096*q+3049 := by omega
  have hr0 : Reach (2048*q+1525) (4096*q+3049) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1525_0 q hr0

#print axioms blank_halt_not_1525_mod2048

/-- Exact inverse-tree certificate for the all-natural 1609 mod2048
terminal family; every leaf contradicts an authentic blank-root invariant. -/
private theorem no_1609_10 (q : Nat) :
    ¬ Reach (2720*q+2120) (2752*q+2157) := by
  intro hr
  have ha := reach_allowed (2720*q+2120) (2752*q+2157) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1609_9 (q : Nat) :
    ¬ Reach (2216*q+1727) (3760*q+2941) := by
  intro hr
  have ha := reach_allowed (2216*q+1727) (3760*q+2941) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1609_8 (q : Nat) :
    ¬ Reach (336*q+260) (7520*q+5882) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (336*q+260) (7520*q+5882) (by omega) (by omega) hr
  have xe : x = 2216*q+1727 := by omega
  have ye : y = 3760*q+2941 := by omega
  rw [xe,ye] at hp
  exact no_1609_9 q hp

private theorem no_1609_7 (q : Nat) :
    ¬ Reach (672*q+523) (6848*q+5359) := by
  intro hr
  rcases odd_back (672*q+523) (6848*q+5359) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 336*q+260 := by omega
    have ye : y = 7520*q+5882 := by omega
    rw [xe,ye] at hp
    exact no_1609_8 q hp
  · omega

private theorem no_1609_6 (q : Nat) :
    ¬ Reach (1344*q+1049) (5504*q+4310) := by
  intro hr
  rcases odd_back (1344*q+1049) (5504*q+4310) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 672*q+523 := by omega
    have ye : y = 6848*q+5359 := by omega
    rw [xe,ye] at hp
    exact no_1609_7 q hp
  · have xe : x = 2720*q+2120 := by omega
    have ye : y = 2752*q+2157 := by omega
    rw [xe,ye] at hp
    exact no_1609_10 q hp

private theorem no_1609_5 (q : Nat) :
    ¬ Reach (2688*q+2101) (2816*q+2209) := by
  intro hr
  rcases odd_back (2688*q+2101) (2816*q+2209) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1344*q+1049 := by omega
    have ye : y = 5504*q+4310 := by omega
    rw [xe,ye] at hp
    exact no_1609_6 q hp
  · omega

private theorem no_1609_4 (q : Nat) :
    ¬ Reach (1280*q+1000) (5632*q+4418) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+1000) (5632*q+4418) (by omega) (by omega) hr
  have xe : x = 2688*q+2101 := by omega
  have ye : y = 2816*q+2209 := by omega
  rw [xe,ye] at hp
  exact no_1609_5 q hp

private theorem no_1609_3 (q : Nat) :
    ¬ Reach (2560*q+2003) (3072*q+2415) := by
  intro hr
  rcases odd_back (2560*q+2003) (3072*q+2415) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+1000 := by omega
    have ye : y = 5632*q+4418 := by omega
    rw [xe,ye] at hp
    exact no_1609_4 q hp
  · omega

private theorem no_1609_2 (q : Nat) :
    ¬ Reach (512*q+400) (7168*q+5629) := by
  intro hr
  have ha := reach_allowed (512*q+400) (7168*q+5629) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_1609_1 (q : Nat) :
    ¬ Reach (1024*q+803) (6144*q+4826) := by
  intro hr
  rcases odd_back (1024*q+803) (6144*q+4826) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+400 := by omega
    have ye : y = 7168*q+5629 := by omega
    rw [xe,ye] at hp
    exact no_1609_2 q hp
  · have xe : x = 2560*q+2003 := by omega
    have ye : y = 3072*q+2415 := by omega
    rw [xe,ye] at hp
    exact no_1609_3 q hp

private theorem no_1609_0 (q : Nat) :
    ¬ Reach (2048*q+1609) (4096*q+3217) := by
  intro hr
  rcases odd_back (2048*q+1609) (4096*q+3217) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+803 := by omega
    have ye : y = 6144*q+4826 := by omega
    rw [xe,ye] at hp
    exact no_1609_1 q hp
  · omega

theorem blank_halt_not_1609_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠1609 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+1609 := by dsimp [q]; omega
  have hb : b=4096*q+3217 := by omega
  have hr0 : Reach (2048*q+1609) (4096*q+3217) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1609_0 q hr0

#print axioms blank_halt_not_1609_mod2048

end BB429AutoGroup3

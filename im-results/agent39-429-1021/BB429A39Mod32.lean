import BB429NewResidue
import BB429RootMod32
import Lean.Elab.Tactic.Omega

namespace BB429A39Mod32
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

private theorem no_4433_ROOTFSFFFFFEF (q : Nat) :
    ¬ Reach (4176*q+2252) (24416*q+13188) := by
  intro hr
  have h := reach_allowed (4176*q+2252) (24416*q+13188) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_4433_ROOTFSFFFFFE (q : Nat) :
    ¬ Reach (8352*q+4507) (16064*q+8681) := by
  intro hr
  rcases odd_back (8352*q+4507) (16064*q+8681) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4176*q+2252) := by omega
    have hyb : y = (24416*q+13188) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFSFFFFFEF q hp
  · omega

private theorem no_4433_ROOTFSFFFSFF (q : Nat) :
    ¬ Reach (2208*q+1189) (28352*q+15313) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod32.rooted_not_5_1 n (2208*q+1189) (28352*q+15313) hn (by omega)
  omega

private theorem no_4433_ROOTFSFFFFF (q : Nat) :
    ¬ Reach (320*q+170) (32128*q+17362) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (320*q+170) (32128*q+17362)
    (by omega) (by omega) hr
  have hxa : x = (8352*q+4507) := by omega
  have hyb : y = (16064*q+8681) := by omega
  rw [hxa,hyb] at hp
  exact no_4433_ROOTFSFFFFFE q hp

private theorem no_4433_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+2381) (23936*q+12932) := by
  intro hr
  rcases odd_back (4416*q+2381) (23936*q+12932) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2208*q+1189) := by omega
    have hyb : y = (28352*q+15313) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFSFFFSFF q hp
  · omega

private theorem no_4433_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+343) (31488*q+17019) := by
  intro hr
  rcases odd_back (640*q+343) (31488*q+17019) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (320*q+170) := by omega
    have hyb : y = (32128*q+17362) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFSFFFFF q hp
  · omega

private theorem no_4433_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+4765) (15104*q+8167) := by
  intro hr
  rcases odd_back (8832*q+4765) (15104*q+8167) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+2381) := by omega
    have hyb : y = (23936*q+12932) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFSFFFSF q hp
  · omega

private theorem no_4433_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+689) (30208*q+16330) := by
  intro hr
  rcases odd_back (1280*q+689) (30208*q+16330) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+343) := by omega
    have hyb : y = (31488*q+17019) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+4765) := by omega
    have hyb : y = (15104*q+8167) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFSFFFS q hp

private theorem no_4433_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+1381) (27648*q+14949) := by
  intro hr
  rcases odd_back (2560*q+1381) (27648*q+14949) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+689) := by omega
    have hyb : y = (30208*q+16330) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFSFFF q hp
  · omega

private theorem no_4433_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+2765) (22528*q+12184) := by
  intro hr
  rcases odd_back (5120*q+2765) (22528*q+12184) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+1381) := by omega
    have hyb : y = (27648*q+14949) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFSFF q hp
  · omega

private theorem no_4433_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1106) (28672*q+15513) := by
  intro hr
  have h := reach_allowed (2048*q+1106) (28672*q+15513) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_4433_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+5533) (12288*q+6651) := by
  intro hr
  rcases odd_back (10240*q+5533) (12288*q+6651) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+2765) := by omega
    have hyb : y = (22528*q+12184) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFSF q hp
  · omega

private theorem no_4433_ROOTF (q : Nat) :
    ¬ Reach (4096*q+2215) (24576*q+13298) := by
  intro hr
  rcases odd_back (4096*q+2215) (24576*q+13298) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1106) := by omega
    have hyb : y = (28672*q+15513) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFF q hp
  · have hxa : x = (10240*q+5533) := by omega
    have hyb : y = (12288*q+6651) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTFS q hp

private theorem no_4433_ROOT (q : Nat) :
    ¬ Reach (8192*q+4433) (16384*q+8865) := by
  intro hr
  rcases odd_back (8192*q+4433) (16384*q+8865) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+2215) := by omega
    have hyb : y = (24576*q+13298) := by omega
    rw [hxa,hyb] at hp
    exact no_4433_ROOTF q hp
  · omega

theorem blank_halt_not_4433_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 4433 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+4433 := by dsimp [q]; omega
  have hb : b=16384*q+8865 := by omega
  have ht : Reach (8192*q+4433) (16384*q+8865) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_4433_ROOT q ht

#print axioms blank_halt_not_4433_mod8192


private theorem no_5193_ROOTFSFEFFFE (q : Nat) :
    ¬ Reach (8864*q+5605) (15040*q+9521) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod32.rooted_not_5_1 n (8864*q+5605) (15040*q+9521) hn (by omega)
  omega

private theorem no_5193_ROOTFSFEFFF (q : Nat) :
    ¬ Reach (1344*q+848) (30080*q+19042) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1344*q+848) (30080*q+19042)
    (by omega) (by omega) hr
  have hxa : x = (8864*q+5605) := by omega
  have hyb : y = (15040*q+9521) := by omega
  rw [hxa,hyb] at hp
  exact no_5193_ROOTFSFEFFFE q hp

private theorem no_5193_ROOTFSFEFF (q : Nat) :
    ¬ Reach (2688*q+1699) (27392*q+17343) := by
  intro hr
  rcases odd_back (2688*q+1699) (27392*q+17343) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1344*q+848) := by omega
    have hyb : y = (30080*q+19042) := by omega
    rw [hxa,hyb] at hp
    exact no_5193_ROOTFSFEFFF q hp
  · omega

private theorem no_5193_ROOTFSFEFS (q : Nat) :
    ¬ Reach (10880*q+6880) (11008*q+6973) := by
  intro hr
  have h := reach_allowed (10880*q+6880) (11008*q+6973) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_5193_ROOTFSFEF (q : Nat) :
    ¬ Reach (5376*q+3401) (22016*q+13942) := by
  intro hr
  rcases odd_back (5376*q+3401) (22016*q+13942) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2688*q+1699) := by omega
    have hyb : y = (27392*q+17343) := by omega
    rw [hxa,hyb] at hp
    exact no_5193_ROOTFSFEFF q hp
  · have hxa : x = (10880*q+6880) := by omega
    have hyb : y = (11008*q+6973) := by omega
    rw [hxa,hyb] at hp
    exact no_5193_ROOTFSFEFS q hp

private theorem no_5193_ROOTFSFE (q : Nat) :
    ¬ Reach (10752*q+6805) (11264*q+7137) := by
  intro hr
  rcases odd_back (10752*q+6805) (11264*q+7137) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5376*q+3401) := by omega
    have hyb : y = (22016*q+13942) := by omega
    rw [hxa,hyb] at hp
    exact no_5193_ROOTFSFEF q hp
  · omega

private theorem no_5193_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+3240) (22528*q+14274) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+3240) (22528*q+14274)
    (by omega) (by omega) hr
  have hxa : x = (10752*q+6805) := by omega
  have hyb : y = (11264*q+7137) := by omega
  rw [hxa,hyb] at hp
  exact no_5193_ROOTFSFE q hp

private theorem no_5193_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1296) (28672*q+18173) := by
  intro hr
  have h := reach_allowed (2048*q+1296) (28672*q+18173) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_5193_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+6483) (12288*q+7791) := by
  intro hr
  rcases odd_back (10240*q+6483) (12288*q+7791) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+3240) := by omega
    have hyb : y = (22528*q+14274) := by omega
    rw [hxa,hyb] at hp
    exact no_5193_ROOTFSF q hp
  · omega

private theorem no_5193_ROOTF (q : Nat) :
    ¬ Reach (4096*q+2595) (24576*q+15578) := by
  intro hr
  rcases odd_back (4096*q+2595) (24576*q+15578) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1296) := by omega
    have hyb : y = (28672*q+18173) := by omega
    rw [hxa,hyb] at hp
    exact no_5193_ROOTFF q hp
  · have hxa : x = (10240*q+6483) := by omega
    have hyb : y = (12288*q+7791) := by omega
    rw [hxa,hyb] at hp
    exact no_5193_ROOTFS q hp

private theorem no_5193_ROOT (q : Nat) :
    ¬ Reach (8192*q+5193) (16384*q+10385) := by
  intro hr
  rcases odd_back (8192*q+5193) (16384*q+10385) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+2595) := by omega
    have hyb : y = (24576*q+15578) := by omega
    rw [hxa,hyb] at hp
    exact no_5193_ROOTF q hp
  · omega

theorem blank_halt_not_5193_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 5193 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+5193 := by dsimp [q]; omega
  have hb : b=16384*q+10385 := by omega
  have ht : Reach (8192*q+5193) (16384*q+10385) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_5193_ROOT q ht

#print axioms blank_halt_not_5193_mod8192


private theorem no_6069_ROOTFFFEFSFE (q : Nat) :
    ¬ Reach (10784*q+7973) (11200*q+8289) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod32.rooted_not_5_1 n (10784*q+7973) (11200*q+8289) hn (by omega)
  omega

private theorem no_6069_ROOTFFFEFSF (q : Nat) :
    ¬ Reach (5184*q+3832) (22400*q+16578) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5184*q+3832) (22400*q+16578)
    (by omega) (by omega) hr
  have hxa : x = (10784*q+7973) := by omega
  have hyb : y = (11200*q+8289) := by omega
  rw [hxa,hyb] at hp
  exact no_6069_ROOTFFFEFSFE q hp

private theorem no_6069_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+1608) (28416*q+21037) := by
  intro hr
  have h := reach_allowed (2176*q+1608) (28416*q+21037) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6069_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+7667) (12032*q+8911) := by
  intro hr
  rcases odd_back (10368*q+7667) (12032*q+8911) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5184*q+3832) := by omega
    have hyb : y = (22400*q+16578) := by omega
    rw [hxa,hyb] at hp
    exact no_6069_ROOTFFFEFSF q hp
  · omega

private theorem no_6069_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+3219) (24064*q+17818) := by
  intro hr
  rcases odd_back (4352*q+3219) (24064*q+17818) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+1608) := by omega
    have hyb : y = (28416*q+21037) := by omega
    rw [hxa,hyb] at hp
    exact no_6069_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+7667) := by omega
    have hyb : y = (12032*q+8911) := by omega
    rw [hxa,hyb] at hp
    exact no_6069_ROOTFFFEFS q hp

private theorem no_6069_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+6441) (15360*q+11377) := by
  intro hr
  rcases odd_back (8704*q+6441) (15360*q+11377) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+3219) := by omega
    have hyb : y = (24064*q+17818) := by omega
    rw [hxa,hyb] at hp
    exact no_6069_ROOTFFFEF q hp
  · omega

private theorem no_6069_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+756) (30720*q+22754) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+756) (30720*q+22754)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+6441) := by omega
  have hyb : y = (15360*q+11377) := by omega
  rw [hxa,hyb] at hp
  exact no_6069_ROOTFFFE q hp

private theorem no_6069_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1515) (28672*q+21239) := by
  intro hr
  rcases odd_back (2048*q+1515) (28672*q+21239) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+756) := by omega
    have hyb : y = (30720*q+22754) := by omega
    rw [hxa,hyb] at hp
    exact no_6069_ROOTFFF q hp
  · omega

private theorem no_6069_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+7578) (12288*q+9105) := by
  intro hr
  have h := reach_allowed (10240*q+7578) (12288*q+9105) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6069_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3033) (24576*q+18206) := by
  intro hr
  rcases odd_back (4096*q+3033) (24576*q+18206) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1515) := by omega
    have hyb : y = (28672*q+21239) := by omega
    rw [hxa,hyb] at hp
    exact no_6069_ROOTFF q hp
  · have hxa : x = (10240*q+7578) := by omega
    have hyb : y = (12288*q+9105) := by omega
    rw [hxa,hyb] at hp
    exact no_6069_ROOTFS q hp

private theorem no_6069_ROOT (q : Nat) :
    ¬ Reach (8192*q+6069) (16384*q+12137) := by
  intro hr
  rcases odd_back (8192*q+6069) (16384*q+12137) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3033) := by omega
    have hyb : y = (24576*q+18206) := by omega
    rw [hxa,hyb] at hp
    exact no_6069_ROOTF q hp
  · omega

theorem blank_halt_not_6069_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 6069 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+6069 := by dsimp [q]; omega
  have hb : b=16384*q+12137 := by omega
  have ht : Reach (8192*q+6069) (16384*q+12137) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_6069_ROOT q ht

#print axioms blank_halt_not_6069_mod8192

end BB429A39Mod32

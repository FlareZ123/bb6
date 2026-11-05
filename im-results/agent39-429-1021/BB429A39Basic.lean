import BB429NewResidue
import BB429RootMod16
import Lean.Elab.Tactic.Omega

namespace BB429A39Basic
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

private theorem no_3721_ROOTFSFEFSFFFF (q : Nat) :
    ¬ Reach (680*q+305) (31408*q+14223) := by
  intro hr
  have h := reach_allowed (680*q+305) (31408*q+14223) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_3721_ROOTFSFEFSFFFS (q : Nat) :
    ¬ Reach (8872*q+4009) (15024*q+6807) := by
  intro hr
  have h := reach_allowed (8872*q+4009) (15024*q+6807) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_3721_ROOTFSFEFSFFF (q : Nat) :
    ¬ Reach (1360*q+613) (30048*q+13610) := by
  intro hr
  rcases odd_back (1360*q+613) (30048*q+13610) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (680*q+305) := by omega
    have hyb : y = (31408*q+14223) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFSFEFSFFFF q hp
  · have hxa : x = (8872*q+4009) := by omega
    have hyb : y = (15024*q+6807) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFSFEFSFFFS q hp

private theorem no_3721_ROOTFSFEFSFF (q : Nat) :
    ¬ Reach (2720*q+1229) (27328*q+12381) := by
  intro hr
  rcases odd_back (2720*q+1229) (27328*q+12381) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1360*q+613) := by omega
    have hyb : y = (30048*q+13610) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFSFEFSFFF q hp
  · omega

private theorem no_3721_ROOTFSFEFSF (q : Nat) :
    ¬ Reach (5440*q+2461) (21888*q+9920) := by
  intro hr
  rcases odd_back (5440*q+2461) (21888*q+9920) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2720*q+1229) := by omega
    have hyb : y = (27328*q+12381) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFSFEFSFF q hp
  · omega

private theorem no_3721_ROOTFSFEFF (q : Nat) :
    ¬ Reach (2688*q+1216) (27392*q+12421) := by
  intro hr
  have h := reach_allowed (2688*q+1216) (27392*q+12421) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_3721_ROOTFSFEFS (q : Nat) :
    ¬ Reach (10880*q+4925) (11008*q+4995) := by
  intro hr
  rcases odd_back (10880*q+4925) (11008*q+4995) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5440*q+2461) := by omega
    have hyb : y = (21888*q+9920) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFSFEFSF q hp
  · omega

private theorem no_3721_ROOTFSFEF (q : Nat) :
    ¬ Reach (5376*q+2435) (22016*q+9986) := by
  intro hr
  rcases odd_back (5376*q+2435) (22016*q+9986) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2688*q+1216) := by omega
    have hyb : y = (27392*q+12421) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFSFEFF q hp
  · have hxa : x = (10880*q+4925) := by omega
    have hyb : y = (11008*q+4995) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFSFEFS q hp

private theorem no_3721_ROOTFSFE (q : Nat) :
    ¬ Reach (10752*q+4873) (11264*q+5113) := by
  intro hr
  rcases odd_back (10752*q+4873) (11264*q+5113) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5376*q+2435) := by omega
    have hyb : y = (22016*q+9986) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFSFEF q hp
  · omega

private theorem no_3721_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+2320) (22528*q+10226) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+2320) (22528*q+10226)
    (by omega) (by omega) hr
  have hxa : x = (10752*q+4873) := by omega
  have hyb : y = (11264*q+5113) := by omega
  rw [hxa,hyb] at hp
  exact no_3721_ROOTFSFE q hp

private theorem no_3721_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+928) (28672*q+13021) := by
  intro hr
  have h := reach_allowed (2048*q+928) (28672*q+13021) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_3721_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+4643) (12288*q+5583) := by
  intro hr
  rcases odd_back (10240*q+4643) (12288*q+5583) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+2320) := by omega
    have hyb : y = (22528*q+10226) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFSF q hp
  · omega

private theorem no_3721_ROOTF (q : Nat) :
    ¬ Reach (4096*q+1859) (24576*q+11162) := by
  intro hr
  rcases odd_back (4096*q+1859) (24576*q+11162) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+928) := by omega
    have hyb : y = (28672*q+13021) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFF q hp
  · have hxa : x = (10240*q+4643) := by omega
    have hyb : y = (12288*q+5583) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTFS q hp

private theorem no_3721_ROOT (q : Nat) :
    ¬ Reach (8192*q+3721) (16384*q+7441) := by
  intro hr
  rcases odd_back (8192*q+3721) (16384*q+7441) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+1859) := by omega
    have hyb : y = (24576*q+11162) := by omega
    rw [hxa,hyb] at hp
    exact no_3721_ROOTF q hp
  · omega

theorem blank_halt_not_3721_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 3721 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+3721 := by dsimp [q]; omega
  have hb : b=16384*q+7441 := by omega
  have ht : Reach (8192*q+3721) (16384*q+7441) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_3721_ROOT q ht

#print axioms blank_halt_not_3721_mod8192


private theorem no_4561_ROOTFSFFFSFEFF (q : Nat) :
    ¬ Reach (2600*q+1441) (27568*q+15311) := by
  intro hr
  have h := reach_allowed (2600*q+1441) (27568*q+15311) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_4561_ROOTFSFFFSFEFS (q : Nat) :
    ¬ Reach (10792*q+5985) (11184*q+6215) := by
  intro hr
  have h := reach_allowed (10792*q+5985) (11184*q+6215) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_4561_ROOTFSFFFSFEF (q : Nat) :
    ¬ Reach (5200*q+2885) (22368*q+12426) := by
  intro hr
  rcases odd_back (5200*q+2885) (22368*q+12426) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2600*q+1441) := by omega
    have hyb : y = (27568*q+15311) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFSFFFSFEFF q hp
  · have hxa : x = (10792*q+5985) := by omega
    have hyb : y = (11184*q+6215) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFSFFFSFEFS q hp

private theorem no_4561_ROOTFSFFFSFE (q : Nat) :
    ¬ Reach (10400*q+5773) (11968*q+6653) := by
  intro hr
  rcases odd_back (10400*q+5773) (11968*q+6653) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5200*q+2885) := by omega
    have hyb : y = (22368*q+12426) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFSFFFSFEF q hp
  · omega

private theorem no_4561_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+2450) (23936*q+13306) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (4416*q+2450) (23936*q+13306)
    (by omega) (by omega) hr
  have hxa : x = (10400*q+5773) := by omega
  have hyb : y = (11968*q+6653) := by omega
  rw [hxa,hyb] at hp
  exact no_4561_ROOTFSFFFSFE q hp

private theorem no_4561_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+353) (31488*q+17511) := by
  intro hr
  have h := reach_allowed (640*q+353) (31488*q+17511) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_4561_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+4903) (15104*q+8403) := by
  intro hr
  rcases odd_back (8832*q+4903) (15104*q+8403) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+2450) := by omega
    have hyb : y = (23936*q+13306) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFSFFFSF q hp
  · omega

private theorem no_4561_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+709) (30208*q+16802) := by
  intro hr
  rcases odd_back (1280*q+709) (30208*q+16802) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+353) := by omega
    have hyb : y = (31488*q+17511) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+4903) := by omega
    have hyb : y = (15104*q+8403) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFSFFFS q hp

private theorem no_4561_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+1421) (27648*q+15381) := by
  intro hr
  rcases odd_back (2560*q+1421) (27648*q+15381) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+709) := by omega
    have hyb : y = (30208*q+16802) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFSFFF q hp
  · omega

private theorem no_4561_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+2845) (22528*q+12536) := by
  intro hr
  rcases odd_back (5120*q+2845) (22528*q+12536) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+1421) := by omega
    have hyb : y = (27648*q+15381) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFSFF q hp
  · omega

private theorem no_4561_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1138) (28672*q+15961) := by
  intro hr
  have h := reach_allowed (2048*q+1138) (28672*q+15961) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_4561_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+5693) (12288*q+6843) := by
  intro hr
  rcases odd_back (10240*q+5693) (12288*q+6843) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+2845) := by omega
    have hyb : y = (22528*q+12536) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFSF q hp
  · omega

private theorem no_4561_ROOTF (q : Nat) :
    ¬ Reach (4096*q+2279) (24576*q+13682) := by
  intro hr
  rcases odd_back (4096*q+2279) (24576*q+13682) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1138) := by omega
    have hyb : y = (28672*q+15961) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFF q hp
  · have hxa : x = (10240*q+5693) := by omega
    have hyb : y = (12288*q+6843) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTFS q hp

private theorem no_4561_ROOT (q : Nat) :
    ¬ Reach (8192*q+4561) (16384*q+9121) := by
  intro hr
  rcases odd_back (8192*q+4561) (16384*q+9121) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+2279) := by omega
    have hyb : y = (24576*q+13682) := by omega
    rw [hxa,hyb] at hp
    exact no_4561_ROOTF q hp
  · omega

theorem blank_halt_not_4561_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 4561 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+4561 := by dsimp [q]; omega
  have hb : b=16384*q+9121 := by omega
  have ht : Reach (8192*q+4561) (16384*q+9121) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_4561_ROOT q ht

#print axioms blank_halt_not_4561_mod8192


private theorem no_1917_ROOTFFFFFSFEFFF (q : Nat) :
    ¬ Reach (1284*q+296) (30200*q+7030) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (1284*q+296) (30200*q+7030) hn (by omega) (by omega)
  omega

private theorem no_1917_ROOTFFFFFSFEFF (q : Nat) :
    ¬ Reach (2568*q+595) (27632*q+6435) := by
  intro hr
  rcases odd_back (2568*q+595) (27632*q+6435) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1284*q+296) := by omega
    have hyb : y = (30200*q+7030) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFFFSFEFFF q hp
  · omega

private theorem no_1917_ROOTFFFFFSFEFS (q : Nat) :
    ¬ Reach (10760*q+2497) (11248*q+2623) := by
  intro hr
  have h := reach_allowed (10760*q+2497) (11248*q+2623) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_1917_ROOTFFFFFSFEF (q : Nat) :
    ¬ Reach (5136*q+1193) (22496*q+5242) := by
  intro hr
  rcases odd_back (5136*q+1193) (22496*q+5242) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2568*q+595) := by omega
    have hyb : y = (27632*q+6435) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFFFSFEFF q hp
  · have hxa : x = (10760*q+2497) := by omega
    have hyb : y = (11248*q+2623) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFFFSFEFS q hp

private theorem no_1917_ROOTFFFFFSFE (q : Nat) :
    ¬ Reach (10272*q+2389) (12224*q+2853) := by
  intro hr
  rcases odd_back (10272*q+2389) (12224*q+2853) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5136*q+1193) := by omega
    have hyb : y = (22496*q+5242) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFFFSFEF q hp
  · omega

private theorem no_1917_ROOTFFFFFFF (q : Nat) :
    ¬ Reach (64*q+12) (32640*q+7622) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (64*q+12) (32640*q+7622) hn (by omega) (by omega)
  omega

private theorem no_1917_ROOTFFFFFSF (q : Nat) :
    ¬ Reach (4160*q+966) (24448*q+5706) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (4160*q+966) (24448*q+5706)
    (by omega) (by omega) hr
  have hxa : x = (10272*q+2389) := by omega
  have hyb : y = (12224*q+2853) := by omega
  rw [hxa,hyb] at hp
  exact no_1917_ROOTFFFFFSFE q hp

private theorem no_1917_ROOTFFFFFF (q : Nat) :
    ¬ Reach (128*q+27) (32512*q+7595) := by
  intro hr
  rcases odd_back (128*q+27) (32512*q+7595) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (64*q+12) := by omega
    have hyb : y = (32640*q+7622) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFFFFF q hp
  · omega

private theorem no_1917_ROOTFFFFFS (q : Nat) :
    ¬ Reach (8320*q+1935) (16128*q+3771) := by
  intro hr
  rcases odd_back (8320*q+1935) (16128*q+3771) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4160*q+966) := by omega
    have hyb : y = (24448*q+5706) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFFFSF q hp
  · omega

private theorem no_1917_ROOTFFFFF (q : Nat) :
    ¬ Reach (256*q+57) (32256*q+7538) := by
  intro hr
  rcases odd_back (256*q+57) (32256*q+7538) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (128*q+27) := by omega
    have hyb : y = (32512*q+7595) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFFFF q hp
  · have hxa : x = (8320*q+1935) := by omega
    have hyb : y = (16128*q+3771) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFFFS q hp

private theorem no_1917_ROOTFFFF (q : Nat) :
    ¬ Reach (512*q+117) (31744*q+7421) := by
  intro hr
  rcases odd_back (512*q+117) (31744*q+7421) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (256*q+57) := by omega
    have hyb : y = (32256*q+7538) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFFF q hp
  · omega

private theorem no_1917_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+237) (30720*q+7184) := by
  intro hr
  rcases odd_back (1024*q+237) (30720*q+7184) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (512*q+117) := by omega
    have hyb : y = (31744*q+7421) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFFF q hp
  · omega

private theorem no_1917_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+477) (28672*q+6707) := by
  intro hr
  rcases odd_back (2048*q+477) (28672*q+6707) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+237) := by omega
    have hyb : y = (30720*q+7184) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFFF q hp
  · omega

private theorem no_1917_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+2388) (12288*q+2877) := by
  intro hr
  have h := reach_allowed (10240*q+2388) (12288*q+2877) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_1917_ROOTF (q : Nat) :
    ¬ Reach (4096*q+957) (24576*q+5750) := by
  intro hr
  rcases odd_back (4096*q+957) (24576*q+5750) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+477) := by omega
    have hyb : y = (28672*q+6707) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFF q hp
  · have hxa : x = (10240*q+2388) := by omega
    have hyb : y = (12288*q+2877) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTFS q hp

private theorem no_1917_ROOT (q : Nat) :
    ¬ Reach (8192*q+1917) (16384*q+3833) := by
  intro hr
  rcases odd_back (8192*q+1917) (16384*q+3833) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+957) := by omega
    have hyb : y = (24576*q+5750) := by omega
    rw [hxa,hyb] at hp
    exact no_1917_ROOTF q hp
  · omega

theorem blank_halt_not_1917_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 1917 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+1917 := by dsimp [q]; omega
  have hb : b=16384*q+3833 := by omega
  have ht : Reach (8192*q+1917) (16384*q+3833) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1917_ROOT q ht

#print axioms blank_halt_not_1917_mod8192


private theorem no_2293_ROOTFFFEFFFFFFF (q : Nat) :
    ¬ Reach (68*q+16) (32632*q+9102) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (68*q+16) (32632*q+9102) hn (by omega) (by omega)
  omega

private theorem no_2293_ROOTFFFEFFFFFSF (q : Nat) :
    ¬ Reach (4164*q+1156) (24440*q+6814) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (4164*q+1156) (24440*q+6814) hn (by omega) (by omega)
  omega

private theorem no_2293_ROOTFFFEFFFFFF (q : Nat) :
    ¬ Reach (136*q+35) (32496*q+9067) := by
  intro hr
  rcases odd_back (136*q+35) (32496*q+9067) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (68*q+16) := by omega
    have hyb : y = (32632*q+9102) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEFFFFFFF q hp
  · omega

private theorem no_2293_ROOTFFFEFFFFFS (q : Nat) :
    ¬ Reach (8328*q+2315) (16112*q+4499) := by
  intro hr
  rcases odd_back (8328*q+2315) (16112*q+4499) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4164*q+1156) := by omega
    have hyb : y = (24440*q+6814) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEFFFFFSF q hp
  · omega

private theorem no_2293_ROOTFFFEFFFFF (q : Nat) :
    ¬ Reach (272*q+73) (32224*q+8994) := by
  intro hr
  rcases odd_back (272*q+73) (32224*q+8994) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (136*q+35) := by omega
    have hyb : y = (32496*q+9067) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEFFFFFF q hp
  · have hxa : x = (8328*q+2315) := by omega
    have hyb : y = (16112*q+4499) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEFFFFFS q hp

private theorem no_2293_ROOTFFFEFFFF (q : Nat) :
    ¬ Reach (544*q+149) (31680*q+8845) := by
  intro hr
  rcases odd_back (544*q+149) (31680*q+8845) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (272*q+73) := by omega
    have hyb : y = (32224*q+8994) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEFFFFF q hp
  · omega

private theorem no_2293_ROOTFFFEFFF (q : Nat) :
    ¬ Reach (1088*q+301) (30592*q+8544) := by
  intro hr
  rcases odd_back (1088*q+301) (30592*q+8544) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (544*q+149) := by omega
    have hyb : y = (31680*q+8845) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEFFFF q hp
  · omega

private theorem no_2293_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+605) (28416*q+7939) := by
  intro hr
  rcases odd_back (2176*q+605) (28416*q+7939) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1088*q+301) := by omega
    have hyb : y = (30592*q+8544) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEFFF q hp
  · omega

private theorem no_2293_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+2888) (12032*q+3365) := by
  intro hr
  have h := reach_allowed (10368*q+2888) (12032*q+3365) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2293_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+1213) (24064*q+6726) := by
  intro hr
  rcases odd_back (4352*q+1213) (24064*q+6726) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+605) := by omega
    have hyb : y = (28416*q+7939) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+2888) := by omega
    have hyb : y = (12032*q+3365) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEFS q hp

private theorem no_2293_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+2429) (15360*q+4297) := by
  intro hr
  rcases odd_back (8704*q+2429) (15360*q+4297) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+1213) := by omega
    have hyb : y = (24064*q+6726) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFFEF q hp
  · omega

private theorem no_2293_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+284) (30720*q+8594) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+284) (30720*q+8594)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+2429) := by omega
  have hyb : y = (15360*q+4297) := by omega
  rw [hxa,hyb] at hp
  exact no_2293_ROOTFFFE q hp

private theorem no_2293_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+571) (28672*q+8023) := by
  intro hr
  rcases odd_back (2048*q+571) (28672*q+8023) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+284) := by omega
    have hyb : y = (30720*q+8594) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFFF q hp
  · omega

private theorem no_2293_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+2858) (12288*q+3441) := by
  intro hr
  have h := reach_allowed (10240*q+2858) (12288*q+3441) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2293_ROOTF (q : Nat) :
    ¬ Reach (4096*q+1145) (24576*q+6878) := by
  intro hr
  rcases odd_back (4096*q+1145) (24576*q+6878) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+571) := by omega
    have hyb : y = (28672*q+8023) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFF q hp
  · have hxa : x = (10240*q+2858) := by omega
    have hyb : y = (12288*q+3441) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTFS q hp

private theorem no_2293_ROOT (q : Nat) :
    ¬ Reach (8192*q+2293) (16384*q+4585) := by
  intro hr
  rcases odd_back (8192*q+2293) (16384*q+4585) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+1145) := by omega
    have hyb : y = (24576*q+6878) := by omega
    rw [hxa,hyb] at hp
    exact no_2293_ROOTF q hp
  · omega

theorem blank_halt_not_2293_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 2293 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+2293 := by dsimp [q]; omega
  have hb : b=16384*q+4585 := by omega
  have ht : Reach (8192*q+2293) (16384*q+4585) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_2293_ROOT q ht

#print axioms blank_halt_not_2293_mod8192


private theorem no_2613_ROOTFFFEFSFFFFF (q : Nat) :
    ¬ Reach (324*q+100) (32120*q+10206) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (324*q+100) (32120*q+10206) hn (by omega) (by omega)
  omega

private theorem no_2613_ROOTFFFEFSFFFF (q : Nat) :
    ¬ Reach (648*q+203) (31472*q+10003) := by
  intro hr
  rcases odd_back (648*q+203) (31472*q+10003) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (324*q+100) := by omega
    have hyb : y = (32120*q+10206) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFFEFSFFFFF q hp
  · omega

private theorem no_2613_ROOTFFFEFSFFFS (q : Nat) :
    ¬ Reach (8840*q+2801) (15088*q+4799) := by
  intro hr
  have h := reach_allowed (8840*q+2801) (15088*q+4799) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2613_ROOTFFFEFSFFF (q : Nat) :
    ¬ Reach (1296*q+409) (30176*q+9594) := by
  intro hr
  rcases odd_back (1296*q+409) (30176*q+9594) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (648*q+203) := by omega
    have hyb : y = (31472*q+10003) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFFEFSFFFF q hp
  · have hxa : x = (8840*q+2801) := by omega
    have hyb : y = (15088*q+4799) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFFEFSFFFS q hp

private theorem no_2613_ROOTFFFEFSFF (q : Nat) :
    ¬ Reach (2592*q+821) (27584*q+8773) := by
  intro hr
  rcases odd_back (2592*q+821) (27584*q+8773) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1296*q+409) := by omega
    have hyb : y = (30176*q+9594) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFFEFSFFF q hp
  · omega

private theorem no_2613_ROOTFFFEFSF (q : Nat) :
    ¬ Reach (5184*q+1645) (22400*q+7128) := by
  intro hr
  rcases odd_back (5184*q+1645) (22400*q+7128) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2592*q+821) := by omega
    have hyb : y = (27584*q+8773) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFFEFSFF q hp
  · omega

private theorem no_2613_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+690) (28416*q+9049) := by
  intro hr
  have h := reach_allowed (2176*q+690) (28416*q+9049) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2613_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+3293) (12032*q+3835) := by
  intro hr
  rcases odd_back (10368*q+3293) (12032*q+3835) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5184*q+1645) := by omega
    have hyb : y = (22400*q+7128) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFFEFSF q hp
  · omega

private theorem no_2613_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+1383) (24064*q+7666) := by
  intro hr
  rcases odd_back (4352*q+1383) (24064*q+7666) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+690) := by omega
    have hyb : y = (28416*q+9049) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+3293) := by omega
    have hyb : y = (12032*q+3835) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFFEFS q hp

private theorem no_2613_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+2769) (15360*q+4897) := by
  intro hr
  rcases odd_back (8704*q+2769) (15360*q+4897) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+1383) := by omega
    have hyb : y = (24064*q+7666) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFFEF q hp
  · omega

private theorem no_2613_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+324) (30720*q+9794) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+324) (30720*q+9794)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+2769) := by omega
  have hyb : y = (15360*q+4897) := by omega
  rw [hxa,hyb] at hp
  exact no_2613_ROOTFFFE q hp

private theorem no_2613_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+651) (28672*q+9143) := by
  intro hr
  rcases odd_back (2048*q+651) (28672*q+9143) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+324) := by omega
    have hyb : y = (30720*q+9794) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFFF q hp
  · omega

private theorem no_2613_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+3258) (12288*q+3921) := by
  intro hr
  have h := reach_allowed (10240*q+3258) (12288*q+3921) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2613_ROOTF (q : Nat) :
    ¬ Reach (4096*q+1305) (24576*q+7838) := by
  intro hr
  rcases odd_back (4096*q+1305) (24576*q+7838) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+651) := by omega
    have hyb : y = (28672*q+9143) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFF q hp
  · have hxa : x = (10240*q+3258) := by omega
    have hyb : y = (12288*q+3921) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTFS q hp

private theorem no_2613_ROOT (q : Nat) :
    ¬ Reach (8192*q+2613) (16384*q+5225) := by
  intro hr
  rcases odd_back (8192*q+2613) (16384*q+5225) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+1305) := by omega
    have hyb : y = (24576*q+7838) := by omega
    rw [hxa,hyb] at hp
    exact no_2613_ROOTF q hp
  · omega

theorem blank_halt_not_2613_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 2613 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+2613 := by dsimp [q]; omega
  have hb : b=16384*q+5225 := by omega
  have ht : Reach (8192*q+2613) (16384*q+5225) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_2613_ROOT q ht

#print axioms blank_halt_not_2613_mod8192


private theorem no_5769_ROOTFSFEFSFFFFF (q : Nat) :
    ¬ Reach (340*q+236) (32088*q+22550) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (340*q+236) (32088*q+22550) hn (by omega) (by omega)
  omega

private theorem no_5769_ROOTFSFEFSFFFSF (q : Nat) :
    ¬ Reach (4436*q+3112) (23896*q+16790) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (4436*q+3112) (23896*q+16790) hn (by omega) (by omega)
  omega

private theorem no_5769_ROOTFSFEFSFFFF (q : Nat) :
    ¬ Reach (680*q+475) (31408*q+22075) := by
  intro hr
  rcases odd_back (680*q+475) (31408*q+22075) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (340*q+236) := by omega
    have hyb : y = (32088*q+22550) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEFSFFFFF q hp
  · omega

private theorem no_5769_ROOTFSFEFSFFFS (q : Nat) :
    ¬ Reach (8872*q+6227) (15024*q+10563) := by
  intro hr
  rcases odd_back (8872*q+6227) (15024*q+10563) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4436*q+3112) := by omega
    have hyb : y = (23896*q+16790) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEFSFFFSF q hp
  · omega

private theorem no_5769_ROOTFSFEFSFFF (q : Nat) :
    ¬ Reach (1360*q+953) (30048*q+21122) := by
  intro hr
  rcases odd_back (1360*q+953) (30048*q+21122) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (680*q+475) := by omega
    have hyb : y = (31408*q+22075) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEFSFFFF q hp
  · have hxa : x = (8872*q+6227) := by omega
    have hyb : y = (15024*q+10563) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEFSFFFS q hp

private theorem no_5769_ROOTFSFEFSFF (q : Nat) :
    ¬ Reach (2720*q+1909) (27328*q+19213) := by
  intro hr
  rcases odd_back (2720*q+1909) (27328*q+19213) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1360*q+953) := by omega
    have hyb : y = (30048*q+21122) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEFSFFF q hp
  · omega

private theorem no_5769_ROOTFSFEFSF (q : Nat) :
    ¬ Reach (5440*q+3821) (21888*q+15392) := by
  intro hr
  rcases odd_back (5440*q+3821) (21888*q+15392) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2720*q+1909) := by omega
    have hyb : y = (27328*q+19213) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEFSFF q hp
  · omega

private theorem no_5769_ROOTFSFEFF (q : Nat) :
    ¬ Reach (2688*q+1888) (27392*q+19269) := by
  intro hr
  have h := reach_allowed (2688*q+1888) (27392*q+19269) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_5769_ROOTFSFEFS (q : Nat) :
    ¬ Reach (10880*q+7645) (11008*q+7747) := by
  intro hr
  rcases odd_back (10880*q+7645) (11008*q+7747) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5440*q+3821) := by omega
    have hyb : y = (21888*q+15392) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEFSF q hp
  · omega

private theorem no_5769_ROOTFSFEF (q : Nat) :
    ¬ Reach (5376*q+3779) (22016*q+15490) := by
  intro hr
  rcases odd_back (5376*q+3779) (22016*q+15490) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2688*q+1888) := by omega
    have hyb : y = (27392*q+19269) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEFF q hp
  · have hxa : x = (10880*q+7645) := by omega
    have hyb : y = (11008*q+7747) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEFS q hp

private theorem no_5769_ROOTFSFE (q : Nat) :
    ¬ Reach (10752*q+7561) (11264*q+7929) := by
  intro hr
  rcases odd_back (10752*q+7561) (11264*q+7929) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5376*q+3779) := by omega
    have hyb : y = (22016*q+15490) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSFEF q hp
  · omega

private theorem no_5769_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+3600) (22528*q+15858) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+3600) (22528*q+15858)
    (by omega) (by omega) hr
  have hxa : x = (10752*q+7561) := by omega
  have hyb : y = (11264*q+7929) := by omega
  rw [hxa,hyb] at hp
  exact no_5769_ROOTFSFE q hp

private theorem no_5769_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1440) (28672*q+20189) := by
  intro hr
  have h := reach_allowed (2048*q+1440) (28672*q+20189) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_5769_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+7203) (12288*q+8655) := by
  intro hr
  rcases odd_back (10240*q+7203) (12288*q+8655) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+3600) := by omega
    have hyb : y = (22528*q+15858) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFSF q hp
  · omega

private theorem no_5769_ROOTF (q : Nat) :
    ¬ Reach (4096*q+2883) (24576*q+17306) := by
  intro hr
  rcases odd_back (4096*q+2883) (24576*q+17306) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1440) := by omega
    have hyb : y = (28672*q+20189) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFF q hp
  · have hxa : x = (10240*q+7203) := by omega
    have hyb : y = (12288*q+8655) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTFS q hp

private theorem no_5769_ROOT (q : Nat) :
    ¬ Reach (8192*q+5769) (16384*q+11537) := by
  intro hr
  rcases odd_back (8192*q+5769) (16384*q+11537) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+2883) := by omega
    have hyb : y = (24576*q+17306) := by omega
    rw [hxa,hyb] at hp
    exact no_5769_ROOTF q hp
  · omega

theorem blank_halt_not_5769_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 5769 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+5769 := by dsimp [q]; omega
  have hb : b=16384*q+11537 := by omega
  have ht : Reach (8192*q+5769) (16384*q+11537) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_5769_ROOT q ht

#print axioms blank_halt_not_5769_mod8192


private theorem no_6609_ROOTFSFFFSFEFFF (q : Nat) :
    ¬ Reach (1300*q+1044) (30168*q+24294) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (1300*q+1044) (30168*q+24294) hn (by omega) (by omega)
  omega

private theorem no_6609_ROOTFSFFFSFEFSF (q : Nat) :
    ¬ Reach (5396*q+4340) (21976*q+17694) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (5396*q+4340) (21976*q+17694) hn (by omega) (by omega)
  omega

private theorem no_6609_ROOTFSFFFSFEFF (q : Nat) :
    ¬ Reach (2600*q+2091) (27568*q+22203) := by
  intro hr
  rcases odd_back (2600*q+2091) (27568*q+22203) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1300*q+1044) := by omega
    have hyb : y = (30168*q+24294) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFFFSFEFFF q hp
  · omega

private theorem no_6609_ROOTFSFFFSFEFS (q : Nat) :
    ¬ Reach (10792*q+8683) (11184*q+9011) := by
  intro hr
  rcases odd_back (10792*q+8683) (11184*q+9011) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5396*q+4340) := by omega
    have hyb : y = (21976*q+17694) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFFFSFEFSF q hp
  · omega

private theorem no_6609_ROOTFSFFFSFEF (q : Nat) :
    ¬ Reach (5200*q+4185) (22368*q+18018) := by
  intro hr
  rcases odd_back (5200*q+4185) (22368*q+18018) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2600*q+2091) := by omega
    have hyb : y = (27568*q+22203) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFFFSFEFF q hp
  · have hxa : x = (10792*q+8683) := by omega
    have hyb : y = (11184*q+9011) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFFFSFEFS q hp

private theorem no_6609_ROOTFSFFFSFE (q : Nat) :
    ¬ Reach (10400*q+8373) (11968*q+9645) := by
  intro hr
  rcases odd_back (10400*q+8373) (11968*q+9645) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5200*q+4185) := by omega
    have hyb : y = (22368*q+18018) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFFFSFEF q hp
  · omega

private theorem no_6609_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+3554) (23936*q+19290) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (4416*q+3554) (23936*q+19290)
    (by omega) (by omega) hr
  have hxa : x = (10400*q+8373) := by omega
  have hyb : y = (11968*q+9645) := by omega
  rw [hxa,hyb] at hp
  exact no_6609_ROOTFSFFFSFE q hp

private theorem no_6609_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+513) (31488*q+25383) := by
  intro hr
  have h := reach_allowed (640*q+513) (31488*q+25383) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6609_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+7111) (15104*q+12179) := by
  intro hr
  rcases odd_back (8832*q+7111) (15104*q+12179) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+3554) := by omega
    have hyb : y = (23936*q+19290) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFFFSF q hp
  · omega

private theorem no_6609_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+1029) (30208*q+24354) := by
  intro hr
  rcases odd_back (1280*q+1029) (30208*q+24354) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+513) := by omega
    have hyb : y = (31488*q+25383) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+7111) := by omega
    have hyb : y = (15104*q+12179) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFFFS q hp

private theorem no_6609_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+2061) (27648*q+22293) := by
  intro hr
  rcases odd_back (2560*q+2061) (27648*q+22293) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+1029) := by omega
    have hyb : y = (30208*q+24354) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFFF q hp
  · omega

private theorem no_6609_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+4125) (22528*q+18168) := by
  intro hr
  rcases odd_back (5120*q+4125) (22528*q+18168) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+2061) := by omega
    have hyb : y = (27648*q+22293) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSFF q hp
  · omega

private theorem no_6609_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1650) (28672*q+23129) := by
  intro hr
  have h := reach_allowed (2048*q+1650) (28672*q+23129) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6609_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+8253) (12288*q+9915) := by
  intro hr
  rcases odd_back (10240*q+8253) (12288*q+9915) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+4125) := by omega
    have hyb : y = (22528*q+18168) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFSF q hp
  · omega

private theorem no_6609_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3303) (24576*q+19826) := by
  intro hr
  rcases odd_back (4096*q+3303) (24576*q+19826) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1650) := by omega
    have hyb : y = (28672*q+23129) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFF q hp
  · have hxa : x = (10240*q+8253) := by omega
    have hyb : y = (12288*q+9915) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTFS q hp

private theorem no_6609_ROOT (q : Nat) :
    ¬ Reach (8192*q+6609) (16384*q+13217) := by
  intro hr
  rcases odd_back (8192*q+6609) (16384*q+13217) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3303) := by omega
    have hyb : y = (24576*q+19826) := by omega
    rw [hxa,hyb] at hp
    exact no_6609_ROOTF q hp
  · omega

theorem blank_halt_not_6609_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 6609 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+6609 := by dsimp [q]; omega
  have hb : b=16384*q+13217 := by omega
  have ht : Reach (8192*q+6609) (16384*q+13217) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_6609_ROOT q ht

#print axioms blank_halt_not_6609_mod8192


private theorem no_6781_ROOTFFFFFFFEFF (q : Nat) :
    ¬ Reach (2056*q+1697) (28656*q+23695) := by
  intro hr
  have h := reach_allowed (2056*q+1697) (28656*q+23695) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6781_ROOTFFFFFFFEFS (q : Nat) :
    ¬ Reach (10248*q+8465) (12272*q+10151) := by
  intro hr
  have h := reach_allowed (10248*q+8465) (12272*q+10151) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6781_ROOTFFFFFFFEF (q : Nat) :
    ¬ Reach (4112*q+3397) (24544*q+20298) := by
  intro hr
  rcases odd_back (4112*q+3397) (24544*q+20298) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2056*q+1697) := by omega
    have hyb : y = (28656*q+23695) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFFFFFFEFF q hp
  · have hxa : x = (10248*q+8465) := by omega
    have hyb : y = (12272*q+10151) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFFFFFFEFS q hp

private theorem no_6781_ROOTFFFFFFFE (q : Nat) :
    ¬ Reach (8224*q+6797) (16320*q+13501) := by
  intro hr
  rcases odd_back (8224*q+6797) (16320*q+13501) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4112*q+3397) := by omega
    have hyb : y = (24544*q+20298) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFFFFFFEF q hp
  · omega

private theorem no_6781_ROOTFFFFFFF (q : Nat) :
    ¬ Reach (64*q+50) (32640*q+27002) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (64*q+50) (32640*q+27002)
    (by omega) (by omega) hr
  have hxa : x = (8224*q+6797) := by omega
  have hyb : y = (16320*q+13501) := by omega
  rw [hxa,hyb] at hp
  exact no_6781_ROOTFFFFFFFE q hp

private theorem no_6781_ROOTFFFFFSF (q : Nat) :
    ¬ Reach (4160*q+3436) (24448*q+20222) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (4160*q+3436) (24448*q+20222) hn (by omega) (by omega)
  omega

private theorem no_6781_ROOTFFFFFF (q : Nat) :
    ¬ Reach (128*q+103) (32512*q+26899) := by
  intro hr
  rcases odd_back (128*q+103) (32512*q+26899) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (64*q+50) := by omega
    have hyb : y = (32640*q+27002) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFFFFFF q hp
  · omega

private theorem no_6781_ROOTFFFFFS (q : Nat) :
    ¬ Reach (8320*q+6875) (16128*q+13347) := by
  intro hr
  rcases odd_back (8320*q+6875) (16128*q+13347) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4160*q+3436) := by omega
    have hyb : y = (24448*q+20222) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFFFFSF q hp
  · omega

private theorem no_6781_ROOTFFFFF (q : Nat) :
    ¬ Reach (256*q+209) (32256*q+26690) := by
  intro hr
  rcases odd_back (256*q+209) (32256*q+26690) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (128*q+103) := by omega
    have hyb : y = (32512*q+26899) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFFFFF q hp
  · have hxa : x = (8320*q+6875) := by omega
    have hyb : y = (16128*q+13347) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFFFFS q hp

private theorem no_6781_ROOTFFFF (q : Nat) :
    ¬ Reach (512*q+421) (31744*q+26269) := by
  intro hr
  rcases odd_back (512*q+421) (31744*q+26269) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (256*q+209) := by omega
    have hyb : y = (32256*q+26690) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFFFF q hp
  · omega

private theorem no_6781_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+845) (30720*q+25424) := by
  intro hr
  rcases odd_back (1024*q+845) (30720*q+25424) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (512*q+421) := by omega
    have hyb : y = (31744*q+26269) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFFF q hp
  · omega

private theorem no_6781_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1693) (28672*q+23731) := by
  intro hr
  rcases odd_back (2048*q+1693) (28672*q+23731) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+845) := by omega
    have hyb : y = (30720*q+25424) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFFF q hp
  · omega

private theorem no_6781_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+8468) (12288*q+10173) := by
  intro hr
  have h := reach_allowed (10240*q+8468) (12288*q+10173) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6781_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3389) (24576*q+20342) := by
  intro hr
  rcases odd_back (4096*q+3389) (24576*q+20342) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1693) := by omega
    have hyb : y = (28672*q+23731) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFF q hp
  · have hxa : x = (10240*q+8468) := by omega
    have hyb : y = (12288*q+10173) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTFS q hp

private theorem no_6781_ROOT (q : Nat) :
    ¬ Reach (8192*q+6781) (16384*q+13561) := by
  intro hr
  rcases odd_back (8192*q+6781) (16384*q+13561) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3389) := by omega
    have hyb : y = (24576*q+20342) := by omega
    rw [hxa,hyb] at hp
    exact no_6781_ROOTF q hp
  · omega

theorem blank_halt_not_6781_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 6781 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+6781 := by dsimp [q]; omega
  have hb : b=16384*q+13561 := by omega
  have ht : Reach (8192*q+6781) (16384*q+13561) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_6781_ROOT q ht

#print axioms blank_halt_not_6781_mod8192


private theorem no_6993_ROOTFSFFFFFEFSF (q : Nat) :
    ¬ Reach (5140*q+4376) (22488*q+19166) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (5140*q+4376) (22488*q+19166) hn (by omega) (by omega)
  omega

private theorem no_6993_ROOTFSFFFFFEFF (q : Nat) :
    ¬ Reach (2088*q+1777) (28592*q+24375) := by
  intro hr
  have h := reach_allowed (2088*q+1777) (28592*q+24375) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6993_ROOTFSFFFFFEFS (q : Nat) :
    ¬ Reach (10280*q+8755) (12208*q+10411) := by
  intro hr
  rcases odd_back (10280*q+8755) (12208*q+10411) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5140*q+4376) := by omega
    have hyb : y = (22488*q+19166) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFFFFEFSF q hp
  · omega

private theorem no_6993_ROOTFSFFFFFEF (q : Nat) :
    ¬ Reach (4176*q+3557) (24416*q+20818) := by
  intro hr
  rcases odd_back (4176*q+3557) (24416*q+20818) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2088*q+1777) := by omega
    have hyb : y = (28592*q+24375) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFFFFEFF q hp
  · have hxa : x = (10280*q+8755) := by omega
    have hyb : y = (12208*q+10411) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFFFFEFS q hp

private theorem no_6993_ROOTFSFFFFFE (q : Nat) :
    ¬ Reach (8352*q+7117) (16064*q+13701) := by
  intro hr
  rcases odd_back (8352*q+7117) (16064*q+13701) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4176*q+3557) := by omega
    have hyb : y = (24416*q+20818) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFFFFEF q hp
  · omega

private theorem no_6993_ROOTFSFFFSFF (q : Nat) :
    ¬ Reach (2208*q+1879) (28352*q+24173) := by
  intro hr
  have h := reach_allowed (2208*q+1879) (28352*q+24173) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6993_ROOTFSFFFFF (q : Nat) :
    ¬ Reach (320*q+270) (32128*q+27402) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (320*q+270) (32128*q+27402)
    (by omega) (by omega) hr
  have hxa : x = (8352*q+7117) := by omega
  have hyb : y = (16064*q+13701) := by omega
  rw [hxa,hyb] at hp
  exact no_6993_ROOTFSFFFFFE q hp

private theorem no_6993_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+3761) (23936*q+20412) := by
  intro hr
  rcases odd_back (4416*q+3761) (23936*q+20412) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2208*q+1879) := by omega
    have hyb : y = (28352*q+24173) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFFSFF q hp
  · omega

private theorem no_6993_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+543) (31488*q+26859) := by
  intro hr
  rcases odd_back (640*q+543) (31488*q+26859) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (320*q+270) := by omega
    have hyb : y = (32128*q+27402) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFFFF q hp
  · omega

private theorem no_6993_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+7525) (15104*q+12887) := by
  intro hr
  rcases odd_back (8832*q+7525) (15104*q+12887) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+3761) := by omega
    have hyb : y = (23936*q+20412) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFFSF q hp
  · omega

private theorem no_6993_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+1089) (30208*q+25770) := by
  intro hr
  rcases odd_back (1280*q+1089) (30208*q+25770) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+543) := by omega
    have hyb : y = (31488*q+26859) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+7525) := by omega
    have hyb : y = (15104*q+12887) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFFS q hp

private theorem no_6993_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+2181) (27648*q+23589) := by
  intro hr
  rcases odd_back (2560*q+2181) (27648*q+23589) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+1089) := by omega
    have hyb : y = (30208*q+25770) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFFF q hp
  · omega

private theorem no_6993_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+4365) (22528*q+19224) := by
  intro hr
  rcases odd_back (5120*q+4365) (22528*q+19224) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+2181) := by omega
    have hyb : y = (27648*q+23589) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSFF q hp
  · omega

private theorem no_6993_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1746) (28672*q+24473) := by
  intro hr
  have h := reach_allowed (2048*q+1746) (28672*q+24473) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6993_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+8733) (12288*q+10491) := by
  intro hr
  rcases odd_back (10240*q+8733) (12288*q+10491) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+4365) := by omega
    have hyb : y = (22528*q+19224) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFSF q hp
  · omega

private theorem no_6993_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3495) (24576*q+20978) := by
  intro hr
  rcases odd_back (4096*q+3495) (24576*q+20978) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1746) := by omega
    have hyb : y = (28672*q+24473) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFF q hp
  · have hxa : x = (10240*q+8733) := by omega
    have hyb : y = (12288*q+10491) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTFS q hp

private theorem no_6993_ROOT (q : Nat) :
    ¬ Reach (8192*q+6993) (16384*q+13985) := by
  intro hr
  rcases odd_back (8192*q+6993) (16384*q+13985) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3495) := by omega
    have hyb : y = (24576*q+20978) := by omega
    rw [hxa,hyb] at hp
    exact no_6993_ROOTF q hp
  · omega

theorem blank_halt_not_6993_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 6993 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+6993 := by dsimp [q]; omega
  have hb : b=16384*q+13985 := by omega
  have ht : Reach (8192*q+6993) (16384*q+13985) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_6993_ROOT q ht

#print axioms blank_halt_not_6993_mod8192


private theorem no_949_ROOTFFFEFSFEFF (q : Nat) :
    ¬ Reach (2696*q+306) (27376*q+3137) := by
  intro hr
  have h := reach_allowed (2696*q+306) (27376*q+3137) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_949_ROOTFFFEFSFEFS (q : Nat) :
    ¬ Reach (10888*q+1239) (10992*q+1263) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_7_7 n (10888*q+1239) (10992*q+1263) hn (by omega)
  omega

private theorem no_949_ROOTFFFEFSFEF (q : Nat) :
    ¬ Reach (5392*q+615) (21984*q+2522) := by
  intro hr
  rcases odd_back (5392*q+615) (21984*q+2522) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2696*q+306) := by omega
    have hyb : y = (27376*q+3137) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFFFEFSFEFF q hp
  · have hxa : x = (10888*q+1239) := by omega
    have hyb : y = (10992*q+1263) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFFFEFSFEFS q hp

private theorem no_949_ROOTFFFEFSFE (q : Nat) :
    ¬ Reach (10784*q+1233) (11200*q+1289) := by
  intro hr
  rcases odd_back (10784*q+1233) (11200*q+1289) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5392*q+615) := by omega
    have hyb : y = (21984*q+2522) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFFFEFSFEF q hp
  · omega

private theorem no_949_ROOTFFFEFSF (q : Nat) :
    ¬ Reach (5184*q+592) (22400*q+2578) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5184*q+592) (22400*q+2578)
    (by omega) (by omega) hr
  have hxa : x = (10784*q+1233) := by omega
  have hyb : y = (11200*q+1289) := by omega
  rw [hxa,hyb] at hp
  exact no_949_ROOTFFFEFSFE q hp

private theorem no_949_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+248) (28416*q+3277) := by
  intro hr
  have h := reach_allowed (2176*q+248) (28416*q+3277) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_949_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+1187) (12032*q+1391) := by
  intro hr
  rcases odd_back (10368*q+1187) (12032*q+1391) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5184*q+592) := by omega
    have hyb : y = (22400*q+2578) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFFFEFSF q hp
  · omega

private theorem no_949_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+499) (24064*q+2778) := by
  intro hr
  rcases odd_back (4352*q+499) (24064*q+2778) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+248) := by omega
    have hyb : y = (28416*q+3277) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+1187) := by omega
    have hyb : y = (12032*q+1391) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFFFEFS q hp

private theorem no_949_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+1001) (15360*q+1777) := by
  intro hr
  rcases odd_back (8704*q+1001) (15360*q+1777) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+499) := by omega
    have hyb : y = (24064*q+2778) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFFFEF q hp
  · omega

private theorem no_949_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+116) (30720*q+3554) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+116) (30720*q+3554)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+1001) := by omega
  have hyb : y = (15360*q+1777) := by omega
  rw [hxa,hyb] at hp
  exact no_949_ROOTFFFE q hp

private theorem no_949_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+235) (28672*q+3319) := by
  intro hr
  rcases odd_back (2048*q+235) (28672*q+3319) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+116) := by omega
    have hyb : y = (30720*q+3554) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFFF q hp
  · omega

private theorem no_949_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+1178) (12288*q+1425) := by
  intro hr
  have h := reach_allowed (10240*q+1178) (12288*q+1425) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_949_ROOTF (q : Nat) :
    ¬ Reach (4096*q+473) (24576*q+2846) := by
  intro hr
  rcases odd_back (4096*q+473) (24576*q+2846) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+235) := by omega
    have hyb : y = (28672*q+3319) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFF q hp
  · have hxa : x = (10240*q+1178) := by omega
    have hyb : y = (12288*q+1425) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTFS q hp

private theorem no_949_ROOT (q : Nat) :
    ¬ Reach (8192*q+949) (16384*q+1897) := by
  intro hr
  rcases odd_back (8192*q+949) (16384*q+1897) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+473) := by omega
    have hyb : y = (24576*q+2846) := by omega
    rw [hxa,hyb] at hp
    exact no_949_ROOTF q hp
  · omega

theorem blank_halt_not_949_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 949 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+949 := by dsimp [q]; omega
  have hb : b=16384*q+1897 := by omega
  have ht : Reach (8192*q+949) (16384*q+1897) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_949_ROOT q ht

#print axioms blank_halt_not_949_mod8192


private theorem no_1033_ROOTFSFEFSFEF (q : Nat) :
    ¬ Reach (5456*q+677) (21856*q+2726) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_5_6 n (5456*q+677) (21856*q+2726) hn (by omega)
  omega

private theorem no_1033_ROOTFSFEFSFE (q : Nat) :
    ¬ Reach (10912*q+1357) (10944*q+1369) := by
  intro hr
  rcases odd_back (10912*q+1357) (10944*q+1369) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5456*q+677) := by omega
    have hyb : y = (21856*q+2726) := by omega
    rw [hxa,hyb] at hp
    exact no_1033_ROOTFSFEFSFEF q hp
  · omega

private theorem no_1033_ROOTFSFEFSF (q : Nat) :
    ¬ Reach (5440*q+676) (21888*q+2738) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5440*q+676) (21888*q+2738)
    (by omega) (by omega) hr
  have hxa : x = (10912*q+1357) := by omega
  have hyb : y = (10944*q+1369) := by omega
  rw [hxa,hyb] at hp
  exact no_1033_ROOTFSFEFSFE q hp

private theorem no_1033_ROOTFSFEFF (q : Nat) :
    ¬ Reach (2688*q+334) (27392*q+3433) := by
  intro hr
  have h := reach_allowed (2688*q+334) (27392*q+3433) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_1033_ROOTFSFEFS (q : Nat) :
    ¬ Reach (10880*q+1355) (11008*q+1383) := by
  intro hr
  rcases odd_back (10880*q+1355) (11008*q+1383) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5440*q+676) := by omega
    have hyb : y = (21888*q+2738) := by omega
    rw [hxa,hyb] at hp
    exact no_1033_ROOTFSFEFSF q hp
  · omega

private theorem no_1033_ROOTFSFEF (q : Nat) :
    ¬ Reach (5376*q+671) (22016*q+2762) := by
  intro hr
  rcases odd_back (5376*q+671) (22016*q+2762) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2688*q+334) := by omega
    have hyb : y = (27392*q+3433) := by omega
    rw [hxa,hyb] at hp
    exact no_1033_ROOTFSFEFF q hp
  · have hxa : x = (10880*q+1355) := by omega
    have hyb : y = (11008*q+1383) := by omega
    rw [hxa,hyb] at hp
    exact no_1033_ROOTFSFEFS q hp

private theorem no_1033_ROOTFSFE (q : Nat) :
    ¬ Reach (10752*q+1345) (11264*q+1417) := by
  intro hr
  rcases odd_back (10752*q+1345) (11264*q+1417) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5376*q+671) := by omega
    have hyb : y = (22016*q+2762) := by omega
    rw [hxa,hyb] at hp
    exact no_1033_ROOTFSFEF q hp
  · omega

private theorem no_1033_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+640) (22528*q+2834) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+640) (22528*q+2834)
    (by omega) (by omega) hr
  have hxa : x = (10752*q+1345) := by omega
  have hyb : y = (11264*q+1417) := by omega
  rw [hxa,hyb] at hp
  exact no_1033_ROOTFSFE q hp

private theorem no_1033_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+256) (28672*q+3613) := by
  intro hr
  have h := reach_allowed (2048*q+256) (28672*q+3613) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_1033_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+1283) (12288*q+1551) := by
  intro hr
  rcases odd_back (10240*q+1283) (12288*q+1551) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+640) := by omega
    have hyb : y = (22528*q+2834) := by omega
    rw [hxa,hyb] at hp
    exact no_1033_ROOTFSF q hp
  · omega

private theorem no_1033_ROOTF (q : Nat) :
    ¬ Reach (4096*q+515) (24576*q+3098) := by
  intro hr
  rcases odd_back (4096*q+515) (24576*q+3098) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+256) := by omega
    have hyb : y = (28672*q+3613) := by omega
    rw [hxa,hyb] at hp
    exact no_1033_ROOTFF q hp
  · have hxa : x = (10240*q+1283) := by omega
    have hyb : y = (12288*q+1551) := by omega
    rw [hxa,hyb] at hp
    exact no_1033_ROOTFS q hp

private theorem no_1033_ROOT (q : Nat) :
    ¬ Reach (8192*q+1033) (16384*q+2065) := by
  intro hr
  rcases odd_back (8192*q+1033) (16384*q+2065) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+515) := by omega
    have hyb : y = (24576*q+3098) := by omega
    rw [hxa,hyb] at hp
    exact no_1033_ROOTF q hp
  · omega

theorem blank_halt_not_1033_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 1033 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+1033 := by dsimp [q]; omega
  have hb : b=16384*q+2065 := by omega
  have ht : Reach (8192*q+1033) (16384*q+2065) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1033_ROOT q ht

#print axioms blank_halt_not_1033_mod8192


private theorem no_5237_ROOTFFFEFFFEF (q : Nat) :
    ¬ Reach (4368*q+2785) (24032*q+15342) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_1_6 n (4368*q+2785) (24032*q+15342) hn (by omega)
  omega

private theorem no_5237_ROOTFFFEFFFE (q : Nat) :
    ¬ Reach (8736*q+5573) (15296*q+9769) := by
  intro hr
  rcases odd_back (8736*q+5573) (15296*q+9769) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4368*q+2785) := by omega
    have hyb : y = (24032*q+15342) := by omega
    rw [hxa,hyb] at hp
    exact no_5237_ROOTFFFEFFFEF q hp
  · omega

private theorem no_5237_ROOTFFFEFFF (q : Nat) :
    ¬ Reach (1088*q+692) (30592*q+19538) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1088*q+692) (30592*q+19538)
    (by omega) (by omega) hr
  have hxa : x = (8736*q+5573) := by omega
  have hyb : y = (15296*q+9769) := by omega
  rw [hxa,hyb] at hp
  exact no_5237_ROOTFFFEFFFE q hp

private theorem no_5237_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+1387) (28416*q+18151) := by
  intro hr
  rcases odd_back (2176*q+1387) (28416*q+18151) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1088*q+692) := by omega
    have hyb : y = (30592*q+19538) := by omega
    rw [hxa,hyb] at hp
    exact no_5237_ROOTFFFEFFF q hp
  · omega

private theorem no_5237_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+6614) (12032*q+7689) := by
  intro hr
  have h := reach_allowed (10368*q+6614) (12032*q+7689) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_5237_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+2777) (24064*q+15374) := by
  intro hr
  rcases odd_back (4352*q+2777) (24064*q+15374) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+1387) := by omega
    have hyb : y = (28416*q+18151) := by omega
    rw [hxa,hyb] at hp
    exact no_5237_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+6614) := by omega
    have hyb : y = (12032*q+7689) := by omega
    rw [hxa,hyb] at hp
    exact no_5237_ROOTFFFEFS q hp

private theorem no_5237_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+5557) (15360*q+9817) := by
  intro hr
  rcases odd_back (8704*q+5557) (15360*q+9817) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+2777) := by omega
    have hyb : y = (24064*q+15374) := by omega
    rw [hxa,hyb] at hp
    exact no_5237_ROOTFFFEF q hp
  · omega

private theorem no_5237_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+652) (30720*q+19634) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+652) (30720*q+19634)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+5557) := by omega
  have hyb : y = (15360*q+9817) := by omega
  rw [hxa,hyb] at hp
  exact no_5237_ROOTFFFE q hp

private theorem no_5237_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1307) (28672*q+18327) := by
  intro hr
  rcases odd_back (2048*q+1307) (28672*q+18327) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+652) := by omega
    have hyb : y = (30720*q+19634) := by omega
    rw [hxa,hyb] at hp
    exact no_5237_ROOTFFF q hp
  · omega

private theorem no_5237_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+6538) (12288*q+7857) := by
  intro hr
  have h := reach_allowed (10240*q+6538) (12288*q+7857) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_5237_ROOTF (q : Nat) :
    ¬ Reach (4096*q+2617) (24576*q+15710) := by
  intro hr
  rcases odd_back (4096*q+2617) (24576*q+15710) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1307) := by omega
    have hyb : y = (28672*q+18327) := by omega
    rw [hxa,hyb] at hp
    exact no_5237_ROOTFF q hp
  · have hxa : x = (10240*q+6538) := by omega
    have hyb : y = (12288*q+7857) := by omega
    rw [hxa,hyb] at hp
    exact no_5237_ROOTFS q hp

private theorem no_5237_ROOT (q : Nat) :
    ¬ Reach (8192*q+5237) (16384*q+10473) := by
  intro hr
  rcases odd_back (8192*q+5237) (16384*q+10473) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+2617) := by omega
    have hyb : y = (24576*q+15710) := by omega
    rw [hxa,hyb] at hp
    exact no_5237_ROOTF q hp
  · omega

theorem blank_halt_not_5237_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 5237 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+5237 := by dsimp [q]; omega
  have hb : b=16384*q+10473 := by omega
  have ht : Reach (8192*q+5237) (16384*q+10473) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_5237_ROOT q ht

#print axioms blank_halt_not_5237_mod8192


private theorem no_5329_ROOTFSFFFFFFF (q : Nat) :
    ¬ Reach (80*q+49) (32608*q+21182) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_1_6 n (80*q+49) (32608*q+21182) hn (by omega)
  omega

private theorem no_5329_ROOTFSFFFFFF (q : Nat) :
    ¬ Reach (160*q+101) (32448*q+21081) := by
  intro hr
  rcases odd_back (160*q+101) (32448*q+21081) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (80*q+49) := by omega
    have hyb : y = (32608*q+21182) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFSFFFFFFF q hp
  · omega

private theorem no_5329_ROOTFSFFFFF (q : Nat) :
    ¬ Reach (320*q+205) (32128*q+20876) := by
  intro hr
  rcases odd_back (320*q+205) (32128*q+20876) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (160*q+101) := by omega
    have hyb : y = (32448*q+21081) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFSFFFFFF q hp
  · omega

private theorem no_5329_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+2864) (23936*q+15550) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (4416*q+2864) (23936*q+15550) hn (by omega) (by omega)
  omega

private theorem no_5329_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+413) (31488*q+20463) := by
  intro hr
  rcases odd_back (640*q+413) (31488*q+20463) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (320*q+205) := by omega
    have hyb : y = (32128*q+20876) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFSFFFFF q hp
  · omega

private theorem no_5329_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+5731) (15104*q+9819) := by
  intro hr
  rcases odd_back (8832*q+5731) (15104*q+9819) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+2864) := by omega
    have hyb : y = (23936*q+15550) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFSFFFSF q hp
  · omega

private theorem no_5329_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+829) (30208*q+19634) := by
  intro hr
  rcases odd_back (1280*q+829) (30208*q+19634) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+413) := by omega
    have hyb : y = (31488*q+20463) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+5731) := by omega
    have hyb : y = (15104*q+9819) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFSFFFS q hp

private theorem no_5329_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+1661) (27648*q+17973) := by
  intro hr
  rcases odd_back (2560*q+1661) (27648*q+17973) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+829) := by omega
    have hyb : y = (30208*q+19634) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFSFFF q hp
  · omega

private theorem no_5329_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+3325) (22528*q+14648) := by
  intro hr
  rcases odd_back (5120*q+3325) (22528*q+14648) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+1661) := by omega
    have hyb : y = (27648*q+17973) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFSFF q hp
  · omega

private theorem no_5329_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1330) (28672*q+18649) := by
  intro hr
  have h := reach_allowed (2048*q+1330) (28672*q+18649) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_5329_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+6653) (12288*q+7995) := by
  intro hr
  rcases odd_back (10240*q+6653) (12288*q+7995) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+3325) := by omega
    have hyb : y = (22528*q+14648) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFSF q hp
  · omega

private theorem no_5329_ROOTF (q : Nat) :
    ¬ Reach (4096*q+2663) (24576*q+15986) := by
  intro hr
  rcases odd_back (4096*q+2663) (24576*q+15986) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1330) := by omega
    have hyb : y = (28672*q+18649) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFF q hp
  · have hxa : x = (10240*q+6653) := by omega
    have hyb : y = (12288*q+7995) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTFS q hp

private theorem no_5329_ROOT (q : Nat) :
    ¬ Reach (8192*q+5329) (16384*q+10657) := by
  intro hr
  rcases odd_back (8192*q+5329) (16384*q+10657) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+2663) := by omega
    have hyb : y = (24576*q+15986) := by omega
    rw [hxa,hyb] at hp
    exact no_5329_ROOTF q hp
  · omega

theorem blank_halt_not_5329_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 5329 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+5329 := by dsimp [q]; omega
  have hb : b=16384*q+10657 := by omega
  have ht : Reach (8192*q+5329) (16384*q+10657) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_5329_ROOT q ht

#print axioms blank_halt_not_5329_mod8192


private theorem no_6261_ROOTFFFEFFFEFF (q : Nat) :
    ¬ Reach (2184*q+1664) (28400*q+21677) := by
  intro hr
  have h := reach_allowed (2184*q+1664) (28400*q+21677) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6261_ROOTFFFEFFFEFS (q : Nat) :
    ¬ Reach (10376*q+7911) (12016*q+9175) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_7_7 n (10376*q+7911) (12016*q+9175) hn (by omega)
  omega

private theorem no_6261_ROOTFFFEFFFEF (q : Nat) :
    ¬ Reach (4368*q+3331) (24032*q+18346) := by
  intro hr
  rcases odd_back (4368*q+3331) (24032*q+18346) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2184*q+1664) := by omega
    have hyb : y = (28400*q+21677) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFFFEFFFEFF q hp
  · have hxa : x = (10376*q+7911) := by omega
    have hyb : y = (12016*q+9175) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFFFEFFFEFS q hp

private theorem no_6261_ROOTFFFEFFFE (q : Nat) :
    ¬ Reach (8736*q+6665) (15296*q+11681) := by
  intro hr
  rcases odd_back (8736*q+6665) (15296*q+11681) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4368*q+3331) := by omega
    have hyb : y = (24032*q+18346) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFFFEFFFEF q hp
  · omega

private theorem no_6261_ROOTFFFEFFF (q : Nat) :
    ¬ Reach (1088*q+828) (30592*q+23362) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1088*q+828) (30592*q+23362)
    (by omega) (by omega) hr
  have hxa : x = (8736*q+6665) := by omega
  have hyb : y = (15296*q+11681) := by omega
  rw [hxa,hyb] at hp
  exact no_6261_ROOTFFFEFFFE q hp

private theorem no_6261_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+1659) (28416*q+21703) := by
  intro hr
  rcases odd_back (2176*q+1659) (28416*q+21703) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1088*q+828) := by omega
    have hyb : y = (30592*q+23362) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFFFEFFF q hp
  · omega

private theorem no_6261_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+7910) (12032*q+9193) := by
  intro hr
  have h := reach_allowed (10368*q+7910) (12032*q+9193) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6261_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+3321) (24064*q+18382) := by
  intro hr
  rcases odd_back (4352*q+3321) (24064*q+18382) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+1659) := by omega
    have hyb : y = (28416*q+21703) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+7910) := by omega
    have hyb : y = (12032*q+9193) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFFFEFS q hp

private theorem no_6261_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+6645) (15360*q+11737) := by
  intro hr
  rcases odd_back (8704*q+6645) (15360*q+11737) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+3321) := by omega
    have hyb : y = (24064*q+18382) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFFFEF q hp
  · omega

private theorem no_6261_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+780) (30720*q+23474) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+780) (30720*q+23474)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+6645) := by omega
  have hyb : y = (15360*q+11737) := by omega
  rw [hxa,hyb] at hp
  exact no_6261_ROOTFFFE q hp

private theorem no_6261_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1563) (28672*q+21911) := by
  intro hr
  rcases odd_back (2048*q+1563) (28672*q+21911) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+780) := by omega
    have hyb : y = (30720*q+23474) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFFF q hp
  · omega

private theorem no_6261_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+7818) (12288*q+9393) := by
  intro hr
  have h := reach_allowed (10240*q+7818) (12288*q+9393) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6261_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3129) (24576*q+18782) := by
  intro hr
  rcases odd_back (4096*q+3129) (24576*q+18782) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1563) := by omega
    have hyb : y = (28672*q+21911) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFF q hp
  · have hxa : x = (10240*q+7818) := by omega
    have hyb : y = (12288*q+9393) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTFS q hp

private theorem no_6261_ROOT (q : Nat) :
    ¬ Reach (8192*q+6261) (16384*q+12521) := by
  intro hr
  rcases odd_back (8192*q+6261) (16384*q+12521) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3129) := by omega
    have hyb : y = (24576*q+18782) := by omega
    rw [hxa,hyb] at hp
    exact no_6261_ROOTF q hp
  · omega

theorem blank_halt_not_6261_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 6261 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+6261 := by dsimp [q]; omega
  have hb : b=16384*q+12521 := by omega
  have ht : Reach (8192*q+6261) (16384*q+12521) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_6261_ROOT q ht

#print axioms blank_halt_not_6261_mod8192


private theorem no_6353_ROOTFSFFFFFFFF (q : Nat) :
    ¬ Reach (40*q+28) (32688*q+25317) := by
  intro hr
  have h := reach_allowed (40*q+28) (32688*q+25317) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6353_ROOTFSFFFFFFFS (q : Nat) :
    ¬ Reach (8232*q+6367) (16304*q+12631) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_7_7 n (8232*q+6367) (16304*q+12631) hn (by omega)
  omega

private theorem no_6353_ROOTFSFFFFFFF (q : Nat) :
    ¬ Reach (80*q+59) (32608*q+25258) := by
  intro hr
  rcases odd_back (80*q+59) (32608*q+25258) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (40*q+28) := by omega
    have hyb : y = (32688*q+25317) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFFFFFFFF q hp
  · have hxa : x = (8232*q+6367) := by omega
    have hyb : y = (16304*q+12631) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFFFFFFFS q hp

private theorem no_6353_ROOTFSFFFFFF (q : Nat) :
    ¬ Reach (160*q+121) (32448*q+25137) := by
  intro hr
  rcases odd_back (160*q+121) (32448*q+25137) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (80*q+59) := by omega
    have hyb : y = (32608*q+25258) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFFFFFFF q hp
  · omega

private theorem no_6353_ROOTFSFFFFF (q : Nat) :
    ¬ Reach (320*q+245) (32128*q+24892) := by
  intro hr
  rcases odd_back (320*q+245) (32128*q+24892) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (160*q+121) := by omega
    have hyb : y = (32448*q+25137) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFFFFFF q hp
  · omega

private theorem no_6353_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+3416) (23936*q+18542) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (4416*q+3416) (23936*q+18542) hn (by omega) (by omega)
  omega

private theorem no_6353_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+493) (31488*q+24399) := by
  intro hr
  rcases odd_back (640*q+493) (31488*q+24399) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (320*q+245) := by omega
    have hyb : y = (32128*q+24892) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFFFFF q hp
  · omega

private theorem no_6353_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+6835) (15104*q+11707) := by
  intro hr
  rcases odd_back (8832*q+6835) (15104*q+11707) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+3416) := by omega
    have hyb : y = (23936*q+18542) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFFFSF q hp
  · omega

private theorem no_6353_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+989) (30208*q+23410) := by
  intro hr
  rcases odd_back (1280*q+989) (30208*q+23410) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+493) := by omega
    have hyb : y = (31488*q+24399) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+6835) := by omega
    have hyb : y = (15104*q+11707) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFFFS q hp

private theorem no_6353_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+1981) (27648*q+21429) := by
  intro hr
  rcases odd_back (2560*q+1981) (27648*q+21429) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+989) := by omega
    have hyb : y = (30208*q+23410) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFFF q hp
  · omega

private theorem no_6353_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+3965) (22528*q+17464) := by
  intro hr
  rcases odd_back (5120*q+3965) (22528*q+17464) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+1981) := by omega
    have hyb : y = (27648*q+21429) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSFF q hp
  · omega

private theorem no_6353_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1586) (28672*q+22233) := by
  intro hr
  have h := reach_allowed (2048*q+1586) (28672*q+22233) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6353_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+7933) (12288*q+9531) := by
  intro hr
  rcases odd_back (10240*q+7933) (12288*q+9531) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+3965) := by omega
    have hyb : y = (22528*q+17464) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFSF q hp
  · omega

private theorem no_6353_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3175) (24576*q+19058) := by
  intro hr
  rcases odd_back (4096*q+3175) (24576*q+19058) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1586) := by omega
    have hyb : y = (28672*q+22233) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFF q hp
  · have hxa : x = (10240*q+7933) := by omega
    have hyb : y = (12288*q+9531) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTFS q hp

private theorem no_6353_ROOT (q : Nat) :
    ¬ Reach (8192*q+6353) (16384*q+12705) := by
  intro hr
  rcases odd_back (8192*q+6353) (16384*q+12705) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3175) := by omega
    have hyb : y = (24576*q+19058) := by omega
    rw [hxa,hyb] at hp
    exact no_6353_ROOTF q hp
  · omega

theorem blank_halt_not_6353_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 6353 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+6353 := by dsimp [q]; omega
  have hb : b=16384*q+12705 := by omega
  have ht : Reach (8192*q+6353) (16384*q+12705) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_6353_ROOT q ht

#print axioms blank_halt_not_6353_mod8192


private theorem no_6481_ROOTFSFFFFFEF (q : Nat) :
    ¬ Reach (4176*q+3296) (24416*q+19292) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (4176*q+3296) (24416*q+19292) hn (by omega) (by omega)
  omega

private theorem no_6481_ROOTFSFFFSFFF (q : Nat) :
    ¬ Reach (1104*q+869) (30560*q+24142) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_5_6 n (1104*q+869) (30560*q+24142) hn (by omega)
  omega

private theorem no_6481_ROOTFSFFFFFE (q : Nat) :
    ¬ Reach (8352*q+6595) (16064*q+12697) := by
  intro hr
  rcases odd_back (8352*q+6595) (16064*q+12697) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4176*q+3296) := by omega
    have hyb : y = (24416*q+19292) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSFFFFFEF q hp
  · omega

private theorem no_6481_ROOTFSFFFSFF (q : Nat) :
    ¬ Reach (2208*q+1741) (28352*q+22401) := by
  intro hr
  rcases odd_back (2208*q+1741) (28352*q+22401) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1104*q+869) := by omega
    have hyb : y = (30560*q+24142) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSFFFSFFF q hp
  · omega

private theorem no_6481_ROOTFSFFFFF (q : Nat) :
    ¬ Reach (320*q+250) (32128*q+25394) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (320*q+250) (32128*q+25394)
    (by omega) (by omega) hr
  have hxa : x = (8352*q+6595) := by omega
  have hyb : y = (16064*q+12697) := by omega
  rw [hxa,hyb] at hp
  exact no_6481_ROOTFSFFFFFE q hp

private theorem no_6481_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+3485) (23936*q+18916) := by
  intro hr
  rcases odd_back (4416*q+3485) (23936*q+18916) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2208*q+1741) := by omega
    have hyb : y = (28352*q+22401) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSFFFSFF q hp
  · omega

private theorem no_6481_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+503) (31488*q+24891) := by
  intro hr
  rcases odd_back (640*q+503) (31488*q+24891) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (320*q+250) := by omega
    have hyb : y = (32128*q+25394) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSFFFFF q hp
  · omega

private theorem no_6481_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+6973) (15104*q+11943) := by
  intro hr
  rcases odd_back (8832*q+6973) (15104*q+11943) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+3485) := by omega
    have hyb : y = (23936*q+18916) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSFFFSF q hp
  · omega

private theorem no_6481_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+1009) (30208*q+23882) := by
  intro hr
  rcases odd_back (1280*q+1009) (30208*q+23882) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+503) := by omega
    have hyb : y = (31488*q+24891) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+6973) := by omega
    have hyb : y = (15104*q+11943) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSFFFS q hp

private theorem no_6481_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+2021) (27648*q+21861) := by
  intro hr
  rcases odd_back (2560*q+2021) (27648*q+21861) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+1009) := by omega
    have hyb : y = (30208*q+23882) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSFFF q hp
  · omega

private theorem no_6481_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+4045) (22528*q+17816) := by
  intro hr
  rcases odd_back (5120*q+4045) (22528*q+17816) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+2021) := by omega
    have hyb : y = (27648*q+21861) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSFF q hp
  · omega

private theorem no_6481_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1618) (28672*q+22681) := by
  intro hr
  have h := reach_allowed (2048*q+1618) (28672*q+22681) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_6481_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+8093) (12288*q+9723) := by
  intro hr
  rcases odd_back (10240*q+8093) (12288*q+9723) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+4045) := by omega
    have hyb : y = (22528*q+17816) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFSF q hp
  · omega

private theorem no_6481_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3239) (24576*q+19442) := by
  intro hr
  rcases odd_back (4096*q+3239) (24576*q+19442) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1618) := by omega
    have hyb : y = (28672*q+22681) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFF q hp
  · have hxa : x = (10240*q+8093) := by omega
    have hyb : y = (12288*q+9723) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTFS q hp

private theorem no_6481_ROOT (q : Nat) :
    ¬ Reach (8192*q+6481) (16384*q+12961) := by
  intro hr
  rcases odd_back (8192*q+6481) (16384*q+12961) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3239) := by omega
    have hyb : y = (24576*q+19442) := by omega
    rw [hxa,hyb] at hp
    exact no_6481_ROOTF q hp
  · omega

theorem blank_halt_not_6481_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 6481 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+6481 := by dsimp [q]; omega
  have hb : b=16384*q+12961 := by omega
  have ht : Reach (8192*q+6481) (16384*q+12961) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_6481_ROOT q ht

#print axioms blank_halt_not_6481_mod8192


private theorem no_7177_ROOTFSFEFSFEF (q : Nat) :
    ¬ Reach (5456*q+4769) (21856*q+19118) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_1_6 n (5456*q+4769) (21856*q+19118) hn (by omega)
  omega

private theorem no_7177_ROOTFSFEFSFE (q : Nat) :
    ¬ Reach (10912*q+9541) (10944*q+9577) := by
  intro hr
  rcases odd_back (10912*q+9541) (10944*q+9577) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5456*q+4769) := by omega
    have hyb : y = (21856*q+19118) := by omega
    rw [hxa,hyb] at hp
    exact no_7177_ROOTFSFEFSFEF q hp
  · omega

private theorem no_7177_ROOTFSFEFSF (q : Nat) :
    ¬ Reach (5440*q+4756) (21888*q+19154) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5440*q+4756) (21888*q+19154)
    (by omega) (by omega) hr
  have hxa : x = (10912*q+9541) := by omega
  have hyb : y = (10944*q+9577) := by omega
  rw [hxa,hyb] at hp
  exact no_7177_ROOTFSFEFSFE q hp

private theorem no_7177_ROOTFSFEFF (q : Nat) :
    ¬ Reach (2688*q+2350) (27392*q+23977) := by
  intro hr
  have h := reach_allowed (2688*q+2350) (27392*q+23977) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_7177_ROOTFSFEFS (q : Nat) :
    ¬ Reach (10880*q+9515) (11008*q+9639) := by
  intro hr
  rcases odd_back (10880*q+9515) (11008*q+9639) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5440*q+4756) := by omega
    have hyb : y = (21888*q+19154) := by omega
    rw [hxa,hyb] at hp
    exact no_7177_ROOTFSFEFSF q hp
  · omega

private theorem no_7177_ROOTFSFEF (q : Nat) :
    ¬ Reach (5376*q+4703) (22016*q+19274) := by
  intro hr
  rcases odd_back (5376*q+4703) (22016*q+19274) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2688*q+2350) := by omega
    have hyb : y = (27392*q+23977) := by omega
    rw [hxa,hyb] at hp
    exact no_7177_ROOTFSFEFF q hp
  · have hxa : x = (10880*q+9515) := by omega
    have hyb : y = (11008*q+9639) := by omega
    rw [hxa,hyb] at hp
    exact no_7177_ROOTFSFEFS q hp

private theorem no_7177_ROOTFSFE (q : Nat) :
    ¬ Reach (10752*q+9409) (11264*q+9865) := by
  intro hr
  rcases odd_back (10752*q+9409) (11264*q+9865) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5376*q+4703) := by omega
    have hyb : y = (22016*q+19274) := by omega
    rw [hxa,hyb] at hp
    exact no_7177_ROOTFSFEF q hp
  · omega

private theorem no_7177_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+4480) (22528*q+19730) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+4480) (22528*q+19730)
    (by omega) (by omega) hr
  have hxa : x = (10752*q+9409) := by omega
  have hyb : y = (11264*q+9865) := by omega
  rw [hxa,hyb] at hp
  exact no_7177_ROOTFSFE q hp

private theorem no_7177_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1792) (28672*q+25117) := by
  intro hr
  have h := reach_allowed (2048*q+1792) (28672*q+25117) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_7177_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+8963) (12288*q+10767) := by
  intro hr
  rcases odd_back (10240*q+8963) (12288*q+10767) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+4480) := by omega
    have hyb : y = (22528*q+19730) := by omega
    rw [hxa,hyb] at hp
    exact no_7177_ROOTFSF q hp
  · omega

private theorem no_7177_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3587) (24576*q+21530) := by
  intro hr
  rcases odd_back (4096*q+3587) (24576*q+21530) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1792) := by omega
    have hyb : y = (28672*q+25117) := by omega
    rw [hxa,hyb] at hp
    exact no_7177_ROOTFF q hp
  · have hxa : x = (10240*q+8963) := by omega
    have hyb : y = (12288*q+10767) := by omega
    rw [hxa,hyb] at hp
    exact no_7177_ROOTFS q hp

private theorem no_7177_ROOT (q : Nat) :
    ¬ Reach (8192*q+7177) (16384*q+14353) := by
  intro hr
  rcases odd_back (8192*q+7177) (16384*q+14353) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3587) := by omega
    have hyb : y = (24576*q+21530) := by omega
    rw [hxa,hyb] at hp
    exact no_7177_ROOTF q hp
  · omega

theorem blank_halt_not_7177_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 7177 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+7177 := by dsimp [q]; omega
  have hb : b=16384*q+14353 := by omega
  have ht : Reach (8192*q+7177) (16384*q+14353) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_7177_ROOT q ht

#print axioms blank_halt_not_7177_mod8192


private theorem no_7241_ROOTFSFEFFFEF (q : Nat) :
    ¬ Reach (4432*q+3909) (23904*q+21102) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_5_6 n (4432*q+3909) (23904*q+21102) hn (by omega)
  omega

private theorem no_7241_ROOTFSFEFFFE (q : Nat) :
    ¬ Reach (8864*q+7821) (15040*q+13281) := by
  intro hr
  rcases odd_back (8864*q+7821) (15040*q+13281) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4432*q+3909) := by omega
    have hyb : y = (23904*q+21102) := by omega
    rw [hxa,hyb] at hp
    exact no_7241_ROOTFSFEFFFEF q hp
  · omega

private theorem no_7241_ROOTFSFEFFF (q : Nat) :
    ¬ Reach (1344*q+1184) (30080*q+26562) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1344*q+1184) (30080*q+26562)
    (by omega) (by omega) hr
  have hxa : x = (8864*q+7821) := by omega
  have hyb : y = (15040*q+13281) := by omega
  rw [hxa,hyb] at hp
  exact no_7241_ROOTFSFEFFFE q hp

private theorem no_7241_ROOTFSFEFF (q : Nat) :
    ¬ Reach (2688*q+2371) (27392*q+24191) := by
  intro hr
  rcases odd_back (2688*q+2371) (27392*q+24191) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1344*q+1184) := by omega
    have hyb : y = (30080*q+26562) := by omega
    rw [hxa,hyb] at hp
    exact no_7241_ROOTFSFEFFF q hp
  · omega

private theorem no_7241_ROOTFSFEFS (q : Nat) :
    ¬ Reach (10880*q+9600) (11008*q+9725) := by
  intro hr
  have h := reach_allowed (10880*q+9600) (11008*q+9725) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_7241_ROOTFSFEF (q : Nat) :
    ¬ Reach (5376*q+4745) (22016*q+19446) := by
  intro hr
  rcases odd_back (5376*q+4745) (22016*q+19446) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2688*q+2371) := by omega
    have hyb : y = (27392*q+24191) := by omega
    rw [hxa,hyb] at hp
    exact no_7241_ROOTFSFEFF q hp
  · have hxa : x = (10880*q+9600) := by omega
    have hyb : y = (11008*q+9725) := by omega
    rw [hxa,hyb] at hp
    exact no_7241_ROOTFSFEFS q hp

private theorem no_7241_ROOTFSFE (q : Nat) :
    ¬ Reach (10752*q+9493) (11264*q+9953) := by
  intro hr
  rcases odd_back (10752*q+9493) (11264*q+9953) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5376*q+4745) := by omega
    have hyb : y = (22016*q+19446) := by omega
    rw [hxa,hyb] at hp
    exact no_7241_ROOTFSFEF q hp
  · omega

private theorem no_7241_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+4520) (22528*q+19906) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+4520) (22528*q+19906)
    (by omega) (by omega) hr
  have hxa : x = (10752*q+9493) := by omega
  have hyb : y = (11264*q+9953) := by omega
  rw [hxa,hyb] at hp
  exact no_7241_ROOTFSFE q hp

private theorem no_7241_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1808) (28672*q+25341) := by
  intro hr
  have h := reach_allowed (2048*q+1808) (28672*q+25341) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_7241_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+9043) (12288*q+10863) := by
  intro hr
  rcases odd_back (10240*q+9043) (12288*q+10863) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+4520) := by omega
    have hyb : y = (22528*q+19906) := by omega
    rw [hxa,hyb] at hp
    exact no_7241_ROOTFSF q hp
  · omega

private theorem no_7241_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3619) (24576*q+21722) := by
  intro hr
  rcases odd_back (4096*q+3619) (24576*q+21722) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1808) := by omega
    have hyb : y = (28672*q+25341) := by omega
    rw [hxa,hyb] at hp
    exact no_7241_ROOTFF q hp
  · have hxa : x = (10240*q+9043) := by omega
    have hyb : y = (12288*q+10863) := by omega
    rw [hxa,hyb] at hp
    exact no_7241_ROOTFS q hp

private theorem no_7241_ROOT (q : Nat) :
    ¬ Reach (8192*q+7241) (16384*q+14481) := by
  intro hr
  rcases odd_back (8192*q+7241) (16384*q+14481) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3619) := by omega
    have hyb : y = (24576*q+21722) := by omega
    rw [hxa,hyb] at hp
    exact no_7241_ROOTF q hp
  · omega

theorem blank_halt_not_7241_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 7241 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+7241 := by dsimp [q]; omega
  have hb : b=16384*q+14481 := by omega
  have ht : Reach (8192*q+7241) (16384*q+14481) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_7241_ROOT q ht

#print axioms blank_halt_not_7241_mod8192


private theorem no_7285_ROOTFFFEFFFEF (q : Nat) :
    ¬ Reach (4368*q+3877) (24032*q+21350) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_5_6 n (4368*q+3877) (24032*q+21350) hn (by omega)
  omega

private theorem no_7285_ROOTFFFEFFFE (q : Nat) :
    ¬ Reach (8736*q+7757) (15296*q+13593) := by
  intro hr
  rcases odd_back (8736*q+7757) (15296*q+13593) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4368*q+3877) := by omega
    have hyb : y = (24032*q+21350) := by omega
    rw [hxa,hyb] at hp
    exact no_7285_ROOTFFFEFFFEF q hp
  · omega

private theorem no_7285_ROOTFFFEFFF (q : Nat) :
    ¬ Reach (1088*q+964) (30592*q+27186) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1088*q+964) (30592*q+27186)
    (by omega) (by omega) hr
  have hxa : x = (8736*q+7757) := by omega
  have hyb : y = (15296*q+13593) := by omega
  rw [hxa,hyb] at hp
  exact no_7285_ROOTFFFEFFFE q hp

private theorem no_7285_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+1931) (28416*q+25255) := by
  intro hr
  rcases odd_back (2176*q+1931) (28416*q+25255) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1088*q+964) := by omega
    have hyb : y = (30592*q+27186) := by omega
    rw [hxa,hyb] at hp
    exact no_7285_ROOTFFFEFFF q hp
  · omega

private theorem no_7285_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+9206) (12032*q+10697) := by
  intro hr
  have h := reach_allowed (10368*q+9206) (12032*q+10697) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_7285_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+3865) (24064*q+21390) := by
  intro hr
  rcases odd_back (4352*q+3865) (24064*q+21390) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+1931) := by omega
    have hyb : y = (28416*q+25255) := by omega
    rw [hxa,hyb] at hp
    exact no_7285_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+9206) := by omega
    have hyb : y = (12032*q+10697) := by omega
    rw [hxa,hyb] at hp
    exact no_7285_ROOTFFFEFS q hp

private theorem no_7285_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+7733) (15360*q+13657) := by
  intro hr
  rcases odd_back (8704*q+7733) (15360*q+13657) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+3865) := by omega
    have hyb : y = (24064*q+21390) := by omega
    rw [hxa,hyb] at hp
    exact no_7285_ROOTFFFEF q hp
  · omega

private theorem no_7285_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+908) (30720*q+27314) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+908) (30720*q+27314)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+7733) := by omega
  have hyb : y = (15360*q+13657) := by omega
  rw [hxa,hyb] at hp
  exact no_7285_ROOTFFFE q hp

private theorem no_7285_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1819) (28672*q+25495) := by
  intro hr
  rcases odd_back (2048*q+1819) (28672*q+25495) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+908) := by omega
    have hyb : y = (30720*q+27314) := by omega
    rw [hxa,hyb] at hp
    exact no_7285_ROOTFFF q hp
  · omega

private theorem no_7285_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+9098) (12288*q+10929) := by
  intro hr
  have h := reach_allowed (10240*q+9098) (12288*q+10929) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_7285_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3641) (24576*q+21854) := by
  intro hr
  rcases odd_back (4096*q+3641) (24576*q+21854) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1819) := by omega
    have hyb : y = (28672*q+25495) := by omega
    rw [hxa,hyb] at hp
    exact no_7285_ROOTFF q hp
  · have hxa : x = (10240*q+9098) := by omega
    have hyb : y = (12288*q+10929) := by omega
    rw [hxa,hyb] at hp
    exact no_7285_ROOTFS q hp

private theorem no_7285_ROOT (q : Nat) :
    ¬ Reach (8192*q+7285) (16384*q+14569) := by
  intro hr
  rcases odd_back (8192*q+7285) (16384*q+14569) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3641) := by omega
    have hyb : y = (24576*q+21854) := by omega
    rw [hxa,hyb] at hp
    exact no_7285_ROOTF q hp
  · omega

theorem blank_halt_not_7285_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 7285 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+7285 := by dsimp [q]; omega
  have hb : b=16384*q+14569 := by omega
  have ht : Reach (8192*q+7285) (16384*q+14569) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_7285_ROOT q ht

#print axioms blank_halt_not_7285_mod8192


private theorem no_7377_ROOTFSFFFFFFF (q : Nat) :
    ¬ Reach (80*q+69) (32608*q+29334) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_5_6 n (80*q+69) (32608*q+29334) hn (by omega)
  omega

private theorem no_7377_ROOTFSFFFFFF (q : Nat) :
    ¬ Reach (160*q+141) (32448*q+29193) := by
  intro hr
  rcases odd_back (160*q+141) (32448*q+29193) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (80*q+69) := by omega
    have hyb : y = (32608*q+29334) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFSFFFFFFF q hp
  · omega

private theorem no_7377_ROOTFSFFFFF (q : Nat) :
    ¬ Reach (320*q+285) (32128*q+28908) := by
  intro hr
  rcases odd_back (320*q+285) (32128*q+28908) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (160*q+141) := by omega
    have hyb : y = (32448*q+29193) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFSFFFFFF q hp
  · omega

private theorem no_7377_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+3968) (23936*q+21534) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootEven8.rooted_positive_even_eight n (4416*q+3968) (23936*q+21534) hn (by omega) (by omega)
  omega

private theorem no_7377_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+573) (31488*q+28335) := by
  intro hr
  rcases odd_back (640*q+573) (31488*q+28335) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (320*q+285) := by omega
    have hyb : y = (32128*q+28908) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFSFFFFF q hp
  · omega

private theorem no_7377_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+7939) (15104*q+13595) := by
  intro hr
  rcases odd_back (8832*q+7939) (15104*q+13595) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+3968) := by omega
    have hyb : y = (23936*q+21534) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFSFFFSF q hp
  · omega

private theorem no_7377_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+1149) (30208*q+27186) := by
  intro hr
  rcases odd_back (1280*q+1149) (30208*q+27186) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+573) := by omega
    have hyb : y = (31488*q+28335) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+7939) := by omega
    have hyb : y = (15104*q+13595) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFSFFFS q hp

private theorem no_7377_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+2301) (27648*q+24885) := by
  intro hr
  rcases odd_back (2560*q+2301) (27648*q+24885) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+1149) := by omega
    have hyb : y = (30208*q+27186) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFSFFF q hp
  · omega

private theorem no_7377_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+4605) (22528*q+20280) := by
  intro hr
  rcases odd_back (5120*q+4605) (22528*q+20280) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+2301) := by omega
    have hyb : y = (27648*q+24885) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFSFF q hp
  · omega

private theorem no_7377_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1842) (28672*q+25817) := by
  intro hr
  have h := reach_allowed (2048*q+1842) (28672*q+25817) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_7377_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+9213) (12288*q+11067) := by
  intro hr
  rcases odd_back (10240*q+9213) (12288*q+11067) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+4605) := by omega
    have hyb : y = (22528*q+20280) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFSF q hp
  · omega

private theorem no_7377_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3687) (24576*q+22130) := by
  intro hr
  rcases odd_back (4096*q+3687) (24576*q+22130) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1842) := by omega
    have hyb : y = (28672*q+25817) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFF q hp
  · have hxa : x = (10240*q+9213) := by omega
    have hyb : y = (12288*q+11067) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTFS q hp

private theorem no_7377_ROOT (q : Nat) :
    ¬ Reach (8192*q+7377) (16384*q+14753) := by
  intro hr
  rcases odd_back (8192*q+7377) (16384*q+14753) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3687) := by omega
    have hyb : y = (24576*q+22130) := by omega
    rw [hxa,hyb] at hp
    exact no_7377_ROOTF q hp
  · omega

theorem blank_halt_not_7377_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 7377 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+7377 := by dsimp [q]; omega
  have hb : b=16384*q+14753 := by omega
  have ht : Reach (8192*q+7377) (16384*q+14753) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_7377_ROOT q ht

#print axioms blank_halt_not_7377_mod8192


private theorem no_8117_ROOTFFFEFSFEF (q : Nat) :
    ¬ Reach (5392*q+5333) (21984*q+21758) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_5_6 n (5392*q+5333) (21984*q+21758) hn (by omega)
  omega

private theorem no_8117_ROOTFFFEFSFE (q : Nat) :
    ¬ Reach (10784*q+10669) (11200*q+11089) := by
  intro hr
  rcases odd_back (10784*q+10669) (11200*q+11089) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5392*q+5333) := by omega
    have hyb : y = (21984*q+21758) := by omega
    rw [hxa,hyb] at hp
    exact no_8117_ROOTFFFEFSFEF q hp
  · omega

private theorem no_8117_ROOTFFFEFSF (q : Nat) :
    ¬ Reach (5184*q+5128) (22400*q+22178) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5184*q+5128) (22400*q+22178)
    (by omega) (by omega) hr
  have hxa : x = (10784*q+10669) := by omega
  have hyb : y = (11200*q+11089) := by omega
  rw [hxa,hyb] at hp
  exact no_8117_ROOTFFFEFSFE q hp

private theorem no_8117_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+2152) (28416*q+28141) := by
  intro hr
  have h := reach_allowed (2176*q+2152) (28416*q+28141) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_8117_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+10259) (12032*q+11919) := by
  intro hr
  rcases odd_back (10368*q+10259) (12032*q+11919) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5184*q+5128) := by omega
    have hyb : y = (22400*q+22178) := by omega
    rw [hxa,hyb] at hp
    exact no_8117_ROOTFFFEFSF q hp
  · omega

private theorem no_8117_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+4307) (24064*q+23834) := by
  intro hr
  rcases odd_back (4352*q+4307) (24064*q+23834) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+2152) := by omega
    have hyb : y = (28416*q+28141) := by omega
    rw [hxa,hyb] at hp
    exact no_8117_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+10259) := by omega
    have hyb : y = (12032*q+11919) := by omega
    rw [hxa,hyb] at hp
    exact no_8117_ROOTFFFEFS q hp

private theorem no_8117_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+8617) (15360*q+15217) := by
  intro hr
  rcases odd_back (8704*q+8617) (15360*q+15217) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+4307) := by omega
    have hyb : y = (24064*q+23834) := by omega
    rw [hxa,hyb] at hp
    exact no_8117_ROOTFFFEF q hp
  · omega

private theorem no_8117_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+1012) (30720*q+30434) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+1012) (30720*q+30434)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+8617) := by omega
  have hyb : y = (15360*q+15217) := by omega
  rw [hxa,hyb] at hp
  exact no_8117_ROOTFFFE q hp

private theorem no_8117_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+2027) (28672*q+28407) := by
  intro hr
  rcases odd_back (2048*q+2027) (28672*q+28407) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+1012) := by omega
    have hyb : y = (30720*q+30434) := by omega
    rw [hxa,hyb] at hp
    exact no_8117_ROOTFFF q hp
  · omega

private theorem no_8117_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+10138) (12288*q+12177) := by
  intro hr
  have h := reach_allowed (10240*q+10138) (12288*q+12177) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_8117_ROOTF (q : Nat) :
    ¬ Reach (4096*q+4057) (24576*q+24350) := by
  intro hr
  rcases odd_back (4096*q+4057) (24576*q+24350) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+2027) := by omega
    have hyb : y = (28672*q+28407) := by omega
    rw [hxa,hyb] at hp
    exact no_8117_ROOTFF q hp
  · have hxa : x = (10240*q+10138) := by omega
    have hyb : y = (12288*q+12177) := by omega
    rw [hxa,hyb] at hp
    exact no_8117_ROOTFS q hp

private theorem no_8117_ROOT (q : Nat) :
    ¬ Reach (8192*q+8117) (16384*q+16233) := by
  intro hr
  rcases odd_back (8192*q+8117) (16384*q+16233) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+4057) := by omega
    have hyb : y = (24576*q+24350) := by omega
    rw [hxa,hyb] at hp
    exact no_8117_ROOTF q hp
  · omega

theorem blank_halt_not_8117_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 8117 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+8117 := by dsimp [q]; omega
  have hb : b=16384*q+16233 := by omega
  have ht : Reach (8192*q+8117) (16384*q+16233) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_8117_ROOT q ht

#print axioms blank_halt_not_8117_mod8192

end BB429A39Basic

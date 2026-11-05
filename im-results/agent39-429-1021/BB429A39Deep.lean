import BB429NewResidue
import BB429RootMod64R2
import Lean.Elab.Tactic.Omega

namespace BB429A39Deep
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

private theorem no_73_ROOTFSFEFFFE (q : Nat) :
    ¬ Reach (8864*q+65) (15040*q+121) := by
  intro hr
  exact BB429RootMod64R0.no_1_25 (8864*q+65) (15040*q+121) hr (by omega) (by omega)

private theorem no_73_ROOTFSFEFFF (q : Nat) :
    ¬ Reach (1344*q+8) (30080*q+242) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1344*q+8) (30080*q+242)
    (by omega) (by omega) hr
  have hxa : x = (8864*q+65) := by omega
  have hyb : y = (15040*q+121) := by omega
  rw [hxa,hyb] at hp
  exact no_73_ROOTFSFEFFFE q hp

private theorem no_73_ROOTFSFEFF (q : Nat) :
    ¬ Reach (2688*q+19) (27392*q+223) := by
  intro hr
  rcases odd_back (2688*q+19) (27392*q+223) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1344*q+8) := by omega
    have hyb : y = (30080*q+242) := by omega
    rw [hxa,hyb] at hp
    exact no_73_ROOTFSFEFFF q hp
  · omega

private theorem no_73_ROOTFSFEFS (q : Nat) :
    ¬ Reach (10880*q+80) (11008*q+93) := by
  intro hr
  have h := reach_allowed (10880*q+80) (11008*q+93) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_73_ROOTFSFEF (q : Nat) :
    ¬ Reach (5376*q+41) (22016*q+182) := by
  intro hr
  rcases odd_back (5376*q+41) (22016*q+182) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2688*q+19) := by omega
    have hyb : y = (27392*q+223) := by omega
    rw [hxa,hyb] at hp
    exact no_73_ROOTFSFEFF q hp
  · have hxa : x = (10880*q+80) := by omega
    have hyb : y = (11008*q+93) := by omega
    rw [hxa,hyb] at hp
    exact no_73_ROOTFSFEFS q hp

private theorem no_73_ROOTFSFE (q : Nat) :
    ¬ Reach (10752*q+85) (11264*q+97) := by
  intro hr
  rcases odd_back (10752*q+85) (11264*q+97) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5376*q+41) := by omega
    have hyb : y = (22016*q+182) := by omega
    rw [hxa,hyb] at hp
    exact no_73_ROOTFSFEF q hp
  · omega

private theorem no_73_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+40) (22528*q+194) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+40) (22528*q+194)
    (by omega) (by omega) hr
  have hxa : x = (10752*q+85) := by omega
  have hyb : y = (11264*q+97) := by omega
  rw [hxa,hyb] at hp
  exact no_73_ROOTFSFE q hp

private theorem no_73_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+16) (28672*q+253) := by
  intro hr
  have h := reach_allowed (2048*q+16) (28672*q+253) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_73_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+83) (12288*q+111) := by
  intro hr
  rcases odd_back (10240*q+83) (12288*q+111) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+40) := by omega
    have hyb : y = (22528*q+194) := by omega
    rw [hxa,hyb] at hp
    exact no_73_ROOTFSF q hp
  · omega

private theorem no_73_ROOTF (q : Nat) :
    ¬ Reach (4096*q+35) (24576*q+218) := by
  intro hr
  rcases odd_back (4096*q+35) (24576*q+218) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+16) := by omega
    have hyb : y = (28672*q+253) := by omega
    rw [hxa,hyb] at hp
    exact no_73_ROOTFF q hp
  · have hxa : x = (10240*q+83) := by omega
    have hyb : y = (12288*q+111) := by omega
    rw [hxa,hyb] at hp
    exact no_73_ROOTFS q hp

private theorem no_73_ROOT (q : Nat) :
    ¬ Reach (8192*q+73) (16384*q+145) := by
  intro hr
  rcases odd_back (8192*q+73) (16384*q+145) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+35) := by omega
    have hyb : y = (24576*q+218) := by omega
    rw [hxa,hyb] at hp
    exact no_73_ROOTF q hp
  · omega

theorem blank_halt_not_73_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 73 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+73 := by dsimp [q]; omega
  have hb : b=16384*q+145 := by omega
  have ht : Reach (8192*q+73) (16384*q+145) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_73_ROOT q ht

#print axioms blank_halt_not_73_mod8192


private theorem no_1361_ROOTFSFFFFFE (q : Nat) :
    ¬ Reach (8352*q+1375) (16064*q+2657) := by
  intro hr
  have h := reach_allowed (8352*q+1375) (16064*q+2657) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_1361_ROOTFSFFFFF (q : Nat) :
    ¬ Reach (320*q+50) (32128*q+5314) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (320*q+50) (32128*q+5314)
    (by omega) (by omega) hr
  have hxa : x = (8352*q+1375) := by omega
  have hyb : y = (16064*q+2657) := by omega
  rw [hxa,hyb] at hp
  exact no_1361_ROOTFSFFFFFE q hp

private theorem no_1361_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+725) (23936*q+3956) := by
  intro hr
  exact BB429RootMod64R2.no_21_20 (4416*q+725) (23936*q+3956) hr (by omega) (by omega)

private theorem no_1361_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+103) (31488*q+5211) := by
  intro hr
  rcases odd_back (640*q+103) (31488*q+5211) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (320*q+50) := by omega
    have hyb : y = (32128*q+5314) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTFSFFFFF q hp
  · omega

private theorem no_1361_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+1453) (15104*q+2503) := by
  intro hr
  rcases odd_back (8832*q+1453) (15104*q+2503) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+725) := by omega
    have hyb : y = (23936*q+3956) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTFSFFFSF q hp
  · omega

private theorem no_1361_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+209) (30208*q+5002) := by
  intro hr
  rcases odd_back (1280*q+209) (30208*q+5002) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+103) := by omega
    have hyb : y = (31488*q+5211) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+1453) := by omega
    have hyb : y = (15104*q+2503) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTFSFFFS q hp

private theorem no_1361_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+421) (27648*q+4581) := by
  intro hr
  rcases odd_back (2560*q+421) (27648*q+4581) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+209) := by omega
    have hyb : y = (30208*q+5002) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTFSFFF q hp
  · omega

private theorem no_1361_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+845) (22528*q+3736) := by
  intro hr
  rcases odd_back (5120*q+845) (22528*q+3736) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+421) := by omega
    have hyb : y = (27648*q+4581) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTFSFF q hp
  · omega

private theorem no_1361_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+338) (28672*q+4761) := by
  intro hr
  have h := reach_allowed (2048*q+338) (28672*q+4761) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_1361_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+1693) (12288*q+2043) := by
  intro hr
  rcases odd_back (10240*q+1693) (12288*q+2043) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+845) := by omega
    have hyb : y = (22528*q+3736) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTFSF q hp
  · omega

private theorem no_1361_ROOTF (q : Nat) :
    ¬ Reach (4096*q+679) (24576*q+4082) := by
  intro hr
  rcases odd_back (4096*q+679) (24576*q+4082) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+338) := by omega
    have hyb : y = (28672*q+4761) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTFF q hp
  · have hxa : x = (10240*q+1693) := by omega
    have hyb : y = (12288*q+2043) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTFS q hp

private theorem no_1361_ROOT (q : Nat) :
    ¬ Reach (8192*q+1361) (16384*q+2721) := by
  intro hr
  rcases odd_back (8192*q+1361) (16384*q+2721) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+679) := by omega
    have hyb : y = (24576*q+4082) := by omega
    rw [hxa,hyb] at hp
    exact no_1361_ROOTF q hp
  · omega

theorem blank_halt_not_1361_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 1361 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+1361 := by dsimp [q]; omega
  have hb : b=16384*q+2721 := by omega
  have ht : Reach (8192*q+1361) (16384*q+2721) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_1361_ROOT q ht

#print axioms blank_halt_not_1361_mod8192


private theorem no_2121_ROOTFSFEFFFE (q : Nat) :
    ¬ Reach (8864*q+2281) (15040*q+3881) := by
  intro hr
  exact BB429RootMod64R2.no_9_9 (8864*q+2281) (15040*q+3881) hr (by omega) (by omega)

private theorem no_2121_ROOTFSFEFFF (q : Nat) :
    ¬ Reach (1344*q+344) (30080*q+7762) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1344*q+344) (30080*q+7762)
    (by omega) (by omega) hr
  have hxa : x = (8864*q+2281) := by omega
  have hyb : y = (15040*q+3881) := by omega
  rw [hxa,hyb] at hp
  exact no_2121_ROOTFSFEFFFE q hp

private theorem no_2121_ROOTFSFEFF (q : Nat) :
    ¬ Reach (2688*q+691) (27392*q+7071) := by
  intro hr
  rcases odd_back (2688*q+691) (27392*q+7071) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1344*q+344) := by omega
    have hyb : y = (30080*q+7762) := by omega
    rw [hxa,hyb] at hp
    exact no_2121_ROOTFSFEFFF q hp
  · omega

private theorem no_2121_ROOTFSFEFS (q : Nat) :
    ¬ Reach (10880*q+2800) (11008*q+2845) := by
  intro hr
  have h := reach_allowed (10880*q+2800) (11008*q+2845) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2121_ROOTFSFEF (q : Nat) :
    ¬ Reach (5376*q+1385) (22016*q+5686) := by
  intro hr
  rcases odd_back (5376*q+1385) (22016*q+5686) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2688*q+691) := by omega
    have hyb : y = (27392*q+7071) := by omega
    rw [hxa,hyb] at hp
    exact no_2121_ROOTFSFEFF q hp
  · have hxa : x = (10880*q+2800) := by omega
    have hyb : y = (11008*q+2845) := by omega
    rw [hxa,hyb] at hp
    exact no_2121_ROOTFSFEFS q hp

private theorem no_2121_ROOTFSFE (q : Nat) :
    ¬ Reach (10752*q+2773) (11264*q+2913) := by
  intro hr
  rcases odd_back (10752*q+2773) (11264*q+2913) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5376*q+1385) := by omega
    have hyb : y = (22016*q+5686) := by omega
    rw [hxa,hyb] at hp
    exact no_2121_ROOTFSFEF q hp
  · omega

private theorem no_2121_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+1320) (22528*q+5826) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+1320) (22528*q+5826)
    (by omega) (by omega) hr
  have hxa : x = (10752*q+2773) := by omega
  have hyb : y = (11264*q+2913) := by omega
  rw [hxa,hyb] at hp
  exact no_2121_ROOTFSFE q hp

private theorem no_2121_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+528) (28672*q+7421) := by
  intro hr
  have h := reach_allowed (2048*q+528) (28672*q+7421) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2121_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+2643) (12288*q+3183) := by
  intro hr
  rcases odd_back (10240*q+2643) (12288*q+3183) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+1320) := by omega
    have hyb : y = (22528*q+5826) := by omega
    rw [hxa,hyb] at hp
    exact no_2121_ROOTFSF q hp
  · omega

private theorem no_2121_ROOTF (q : Nat) :
    ¬ Reach (4096*q+1059) (24576*q+6362) := by
  intro hr
  rcases odd_back (4096*q+1059) (24576*q+6362) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+528) := by omega
    have hyb : y = (28672*q+7421) := by omega
    rw [hxa,hyb] at hp
    exact no_2121_ROOTFF q hp
  · have hxa : x = (10240*q+2643) := by omega
    have hyb : y = (12288*q+3183) := by omega
    rw [hxa,hyb] at hp
    exact no_2121_ROOTFS q hp

private theorem no_2121_ROOT (q : Nat) :
    ¬ Reach (8192*q+2121) (16384*q+4241) := by
  intro hr
  rcases odd_back (8192*q+2121) (16384*q+4241) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+1059) := by omega
    have hyb : y = (24576*q+6362) := by omega
    rw [hxa,hyb] at hp
    exact no_2121_ROOTF q hp
  · omega

theorem blank_halt_not_2121_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 2121 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+2121 := by dsimp [q]; omega
  have hb : b=16384*q+4241 := by omega
  have ht : Reach (8192*q+2121) (16384*q+4241) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_2121_ROOT q ht

#print axioms blank_halt_not_2121_mod8192


private theorem no_7505_ROOTFSFFFFFE (q : Nat) :
    ¬ Reach (8352*q+7639) (16064*q+14705) := by
  intro hr
  have h := reach_allowed (8352*q+7639) (16064*q+14705) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_7505_ROOTFSFFFFF (q : Nat) :
    ¬ Reach (320*q+290) (32128*q+29410) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (320*q+290) (32128*q+29410)
    (by omega) (by omega) hr
  have hxa : x = (8352*q+7639) := by omega
  have hyb : y = (16064*q+14705) := by omega
  rw [hxa,hyb] at hp
  exact no_7505_ROOTFSFFFFFE q hp

private theorem no_7505_ROOTFSFFFSF (q : Nat) :
    ¬ Reach (4416*q+4037) (23936*q+21908) := by
  intro hr
  exact BB429RootMod64R0.no_5_20 (4416*q+4037) (23936*q+21908) hr (by omega) (by omega)

private theorem no_7505_ROOTFSFFFF (q : Nat) :
    ¬ Reach (640*q+583) (31488*q+28827) := by
  intro hr
  rcases odd_back (640*q+583) (31488*q+28827) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (320*q+290) := by omega
    have hyb : y = (32128*q+29410) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTFSFFFFF q hp
  · omega

private theorem no_7505_ROOTFSFFFS (q : Nat) :
    ¬ Reach (8832*q+8077) (15104*q+13831) := by
  intro hr
  rcases odd_back (8832*q+8077) (15104*q+13831) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4416*q+4037) := by omega
    have hyb : y = (23936*q+21908) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTFSFFFSF q hp
  · omega

private theorem no_7505_ROOTFSFFF (q : Nat) :
    ¬ Reach (1280*q+1169) (30208*q+27658) := by
  intro hr
  rcases odd_back (1280*q+1169) (30208*q+27658) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (640*q+583) := by omega
    have hyb : y = (31488*q+28827) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTFSFFFF q hp
  · have hxa : x = (8832*q+8077) := by omega
    have hyb : y = (15104*q+13831) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTFSFFFS q hp

private theorem no_7505_ROOTFSFF (q : Nat) :
    ¬ Reach (2560*q+2341) (27648*q+25317) := by
  intro hr
  rcases odd_back (2560*q+2341) (27648*q+25317) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1280*q+1169) := by omega
    have hyb : y = (30208*q+27658) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTFSFFF q hp
  · omega

private theorem no_7505_ROOTFSF (q : Nat) :
    ¬ Reach (5120*q+4685) (22528*q+20632) := by
  intro hr
  rcases odd_back (5120*q+4685) (22528*q+20632) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2560*q+2341) := by omega
    have hyb : y = (27648*q+25317) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTFSFF q hp
  · omega

private theorem no_7505_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+1874) (28672*q+26265) := by
  intro hr
  have h := reach_allowed (2048*q+1874) (28672*q+26265) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_7505_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+9373) (12288*q+11259) := by
  intro hr
  rcases odd_back (10240*q+9373) (12288*q+11259) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5120*q+4685) := by omega
    have hyb : y = (22528*q+20632) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTFSF q hp
  · omega

private theorem no_7505_ROOTF (q : Nat) :
    ¬ Reach (4096*q+3751) (24576*q+22514) := by
  intro hr
  rcases odd_back (4096*q+3751) (24576*q+22514) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+1874) := by omega
    have hyb : y = (28672*q+26265) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTFF q hp
  · have hxa : x = (10240*q+9373) := by omega
    have hyb : y = (12288*q+11259) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTFS q hp

private theorem no_7505_ROOT (q : Nat) :
    ¬ Reach (8192*q+7505) (16384*q+15009) := by
  intro hr
  rcases odd_back (8192*q+7505) (16384*q+15009) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+3751) := by omega
    have hyb : y = (24576*q+22514) := by omega
    rw [hxa,hyb] at hp
    exact no_7505_ROOTF q hp
  · omega

theorem blank_halt_not_7505_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 7505 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+7505 := by dsimp [q]; omega
  have hb : b=16384*q+15009 := by omega
  have ht : Reach (8192*q+7505) (16384*q+15009) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_7505_ROOT q ht

#print axioms blank_halt_not_7505_mod8192

end BB429A39Deep

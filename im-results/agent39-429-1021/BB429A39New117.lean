import BB429NewResidue
import Lean.Elab.Tactic.Omega

namespace BB429A39New117
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 25000000

private theorem no_117_ROOTFFFEFFFEFF (q : Nat) :
    ¬ Reach (2184*q+26) (28400*q+377) := by
  intro hr
  have h := reach_allowed (2184*q+26) (28400*q+377) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_117_ROOTFFFEFFFEFS (q : Nat) :
    ¬ Reach (10376*q+129) (12016*q+163) := by
  intro hr
  have h := reach_allowed (10376*q+129) (12016*q+163) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_117_ROOTFFFEFFFEF (q : Nat) :
    ¬ Reach (4368*q+55) (24032*q+322) := by
  intro hr
  rcases odd_back (4368*q+55) (24032*q+322) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2184*q+26) := by omega
    have hyb : y = (28400*q+377) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFFFEFFFEFF q hp
  · have hxa : x = (10376*q+129) := by omega
    have hyb : y = (12016*q+163) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFFFEFFFEFS q hp

private theorem no_117_ROOTFFFEFFFE (q : Nat) :
    ¬ Reach (8736*q+113) (15296*q+209) := by
  intro hr
  rcases odd_back (8736*q+113) (15296*q+209) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4368*q+55) := by omega
    have hyb : y = (24032*q+322) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFFFEFFFEF q hp
  · omega

private theorem no_117_ROOTFFFEFFF (q : Nat) :
    ¬ Reach (1088*q+12) (30592*q+418) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1088*q+12) (30592*q+418)
    (by omega) (by omega) hr
  have hxa : x = (8736*q+113) := by omega
  have hyb : y = (15296*q+209) := by omega
  rw [hxa,hyb] at hp
  exact no_117_ROOTFFFEFFFE q hp

private theorem no_117_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+27) (28416*q+391) := by
  intro hr
  rcases odd_back (2176*q+27) (28416*q+391) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1088*q+12) := by omega
    have hyb : y = (30592*q+418) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFFFEFFF q hp
  · omega

private theorem no_117_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+134) (12032*q+169) := by
  intro hr
  have h := reach_allowed (10368*q+134) (12032*q+169) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_117_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+57) (24064*q+334) := by
  intro hr
  rcases odd_back (4352*q+57) (24064*q+334) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+27) := by omega
    have hyb : y = (28416*q+391) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+134) := by omega
    have hyb : y = (12032*q+169) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFFFEFS q hp

private theorem no_117_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+117) (15360*q+217) := by
  intro hr
  rcases odd_back (8704*q+117) (15360*q+217) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+57) := by omega
    have hyb : y = (24064*q+334) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFFFEF q hp
  · omega

private theorem no_117_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+12) (30720*q+434) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+12) (30720*q+434)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+117) := by omega
  have hyb : y = (15360*q+217) := by omega
  rw [hxa,hyb] at hp
  exact no_117_ROOTFFFE q hp

private theorem no_117_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+27) (28672*q+407) := by
  intro hr
  rcases odd_back (2048*q+27) (28672*q+407) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+12) := by omega
    have hyb : y = (30720*q+434) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFFF q hp
  · omega

private theorem no_117_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+138) (12288*q+177) := by
  intro hr
  have h := reach_allowed (10240*q+138) (12288*q+177) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_117_ROOTF (q : Nat) :
    ¬ Reach (4096*q+57) (24576*q+350) := by
  intro hr
  rcases odd_back (4096*q+57) (24576*q+350) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+27) := by omega
    have hyb : y = (28672*q+407) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFF q hp
  · have hxa : x = (10240*q+138) := by omega
    have hyb : y = (12288*q+177) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTFS q hp

private theorem no_117_ROOT (q : Nat) :
    ¬ Reach (8192*q+117) (16384*q+233) := by
  intro hr
  rcases odd_back (8192*q+117) (16384*q+233) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+57) := by omega
    have hyb : y = (24576*q+350) := by omega
    rw [hxa,hyb] at hp
    exact no_117_ROOTF q hp
  · omega

theorem blank_halt_not_117_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 117 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+117 := by dsimp [q]; omega
  have hb : b=16384*q+233 := by omega
  have ht : Reach (8192*q+117) (16384*q+233) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_117_ROOT q ht

#print axioms blank_halt_not_117_mod8192


private theorem no_2997_ROOTFFFEFSFEFF (q : Nat) :
    ¬ Reach (2696*q+980) (27376*q+9981) := by
  intro hr
  have h := reach_allowed (2696*q+980) (27376*q+9981) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2997_ROOTFFFEFSFEFS (q : Nat) :
    ¬ Reach (10888*q+3961) (10992*q+4011) := by
  intro hr
  have h := reach_allowed (10888*q+3961) (10992*q+4011) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2997_ROOTFFFEFSFEF (q : Nat) :
    ¬ Reach (5392*q+1963) (21984*q+8018) := by
  intro hr
  rcases odd_back (5392*q+1963) (21984*q+8018) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2696*q+980) := by omega
    have hyb : y = (27376*q+9981) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFFFEFSFEFF q hp
  · have hxa : x = (10888*q+3961) := by omega
    have hyb : y = (10992*q+4011) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFFFEFSFEFS q hp

private theorem no_2997_ROOTFFFEFSFE (q : Nat) :
    ¬ Reach (10784*q+3929) (11200*q+4089) := by
  intro hr
  rcases odd_back (10784*q+3929) (11200*q+4089) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5392*q+1963) := by omega
    have hyb : y = (21984*q+8018) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFFFEFSFEF q hp
  · omega

private theorem no_2997_ROOTFFFEFSF (q : Nat) :
    ¬ Reach (5184*q+1888) (22400*q+8178) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5184*q+1888) (22400*q+8178)
    (by omega) (by omega) hr
  have hxa : x = (10784*q+3929) := by omega
  have hyb : y = (11200*q+4089) := by omega
  rw [hxa,hyb] at hp
  exact no_2997_ROOTFFFEFSFE q hp

private theorem no_2997_ROOTFFFEFF (q : Nat) :
    ¬ Reach (2176*q+792) (28416*q+10381) := by
  intro hr
  have h := reach_allowed (2176*q+792) (28416*q+10381) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2997_ROOTFFFEFS (q : Nat) :
    ¬ Reach (10368*q+3779) (12032*q+4399) := by
  intro hr
  rcases odd_back (10368*q+3779) (12032*q+4399) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (5184*q+1888) := by omega
    have hyb : y = (22400*q+8178) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFFFEFSF q hp
  · omega

private theorem no_2997_ROOTFFFEF (q : Nat) :
    ¬ Reach (4352*q+1587) (24064*q+8794) := by
  intro hr
  rcases odd_back (4352*q+1587) (24064*q+8794) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2176*q+792) := by omega
    have hyb : y = (28416*q+10381) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFFFEFF q hp
  · have hxa : x = (10368*q+3779) := by omega
    have hyb : y = (12032*q+4399) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFFFEFS q hp

private theorem no_2997_ROOTFFFE (q : Nat) :
    ¬ Reach (8704*q+3177) (15360*q+5617) := by
  intro hr
  rcases odd_back (8704*q+3177) (15360*q+5617) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4352*q+1587) := by omega
    have hyb : y = (24064*q+8794) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFFFEF q hp
  · omega

private theorem no_2997_ROOTFFF (q : Nat) :
    ¬ Reach (1024*q+372) (30720*q+11234) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1024*q+372) (30720*q+11234)
    (by omega) (by omega) hr
  have hxa : x = (8704*q+3177) := by omega
  have hyb : y = (15360*q+5617) := by omega
  rw [hxa,hyb] at hp
  exact no_2997_ROOTFFFE q hp

private theorem no_2997_ROOTFF (q : Nat) :
    ¬ Reach (2048*q+747) (28672*q+10487) := by
  intro hr
  rcases odd_back (2048*q+747) (28672*q+10487) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (1024*q+372) := by omega
    have hyb : y = (30720*q+11234) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFFF q hp
  · omega

private theorem no_2997_ROOTFS (q : Nat) :
    ¬ Reach (10240*q+3738) (12288*q+4497) := by
  intro hr
  have h := reach_allowed (10240*q+3738) (12288*q+4497) hr
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_2997_ROOTF (q : Nat) :
    ¬ Reach (4096*q+1497) (24576*q+8990) := by
  intro hr
  rcases odd_back (4096*q+1497) (24576*q+8990) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (2048*q+747) := by omega
    have hyb : y = (28672*q+10487) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFF q hp
  · have hxa : x = (10240*q+3738) := by omega
    have hyb : y = (12288*q+4497) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTFS q hp

private theorem no_2997_ROOT (q : Nat) :
    ¬ Reach (8192*q+2997) (16384*q+5993) := by
  intro hr
  rcases odd_back (8192*q+2997) (16384*q+5993) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxa : x = (4096*q+1497) := by omega
    have hyb : y = (24576*q+8990) := by omega
    rw [hxa,hyb] at hp
    exact no_2997_ROOTF q hp
  · omega

theorem blank_halt_not_2997_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192 ≠ 2997 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+2997 := by dsimp [q]; omega
  have hb : b=16384*q+5993 := by omega
  have ht : Reach (8192*q+2997) (16384*q+5993) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_2997_ROOT q ht

#print axioms blank_halt_not_2997_mod8192

end BB429A39New117

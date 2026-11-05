import BB429RootMod16
import BB429NewResidue
import Lean.Elab.Tactic.Omega

namespace BB429No73
set_option maxRecDepth 30000
set_option maxHeartbeats 30000000
open BB429NewResidue

private theorem no_rootFF (q : Nat) :
    ¬ Reach (2048*q+16) (28672*q+253) := by
  intro hr
  have hh := reach_allowed (2048*q+16) (28672*q+253) hr
  unfold BB429Mod8.Allowed at hh
  omega

private theorem no_rootFSFEFFFEFF (q : Nat) :
    ¬ Reach (2216*q+14) (28336*q+217) := by
  intro hr
  have hh := reach_allowed (2216*q+14) (28336*q+217) hr
  unfold BB429Mod8.Allowed at hh
  omega

private theorem no_rootFSFEFFFEFS (q : Nat) :
    ¬ Reach (10408*q+71) (11952*q+95) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_7_7 n (10408*q+71) (11952*q+95) hn (by omega)
  exact hh (by omega)

private theorem no_rootFSFEFFFEF (q : Nat) :
    ¬ Reach (4432*q+31) (23904*q+186) := by
  intro hr
  rcases odd_back (4432*q+31) (23904*q+186) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=2216*q+14 := by omega
    have he2 : y=28336*q+217 := by omega
    rw [he1,he2] at hp
    exact no_rootFSFEFFFEFF q hp
  · have he1 : x=10408*q+71 := by omega
    have he2 : y=11952*q+95 := by omega
    rw [he1,he2] at hp
    exact no_rootFSFEFFFEFS q hp

private theorem no_rootFSFEFFFE (q : Nat) :
    ¬ Reach (8864*q+65) (15040*q+121) := by
  intro hr
  rcases odd_back (8864*q+65) (15040*q+121) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=4432*q+31 := by omega
    have he2 : y=23904*q+186 := by omega
    rw [he1,he2] at hp
    exact no_rootFSFEFFFEF q hp
  · omega

private theorem no_rootFSFEFFF (q : Nat) :
    ¬ Reach (1344*q+8) (30080*q+242) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (1344*q+8) (30080*q+242)
    (by omega) (by omega) hr
  have he1 : x=8864*q+65 := by omega
  have he2 : y=15040*q+121 := by omega
  rw [he1,he2] at hp
  exact no_rootFSFEFFFE q hp

private theorem no_rootFSFEFF (q : Nat) :
    ¬ Reach (2688*q+19) (27392*q+223) := by
  intro hr
  rcases odd_back (2688*q+19) (27392*q+223) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=1344*q+8 := by omega
    have he2 : y=30080*q+242 := by omega
    rw [he1,he2] at hp
    exact no_rootFSFEFFF q hp
  · omega

private theorem no_rootFSFEFS (q : Nat) :
    ¬ Reach (10880*q+80) (11008*q+93) := by
  intro hr
  have hh := reach_allowed (10880*q+80) (11008*q+93) hr
  unfold BB429Mod8.Allowed at hh
  omega

private theorem no_rootFSFEF (q : Nat) :
    ¬ Reach (5376*q+41) (22016*q+182) := by
  intro hr
  rcases odd_back (5376*q+41) (22016*q+182) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=2688*q+19 := by omega
    have he2 : y=27392*q+223 := by omega
    rw [he1,he2] at hp
    exact no_rootFSFEFF q hp
  · have he1 : x=10880*q+80 := by omega
    have he2 : y=11008*q+93 := by omega
    rw [he1,he2] at hp
    exact no_rootFSFEFS q hp

private theorem no_rootFSFE (q : Nat) :
    ¬ Reach (10752*q+85) (11264*q+97) := by
  intro hr
  rcases odd_back (10752*q+85) (11264*q+97) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=5376*q+41 := by omega
    have he2 : y=22016*q+182 := by omega
    rw [he1,he2] at hp
    exact no_rootFSFEF q hp
  · omega

private theorem no_rootFSF (q : Nat) :
    ¬ Reach (5120*q+40) (22528*q+194) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+40) (22528*q+194)
    (by omega) (by omega) hr
  have he1 : x=10752*q+85 := by omega
  have he2 : y=11264*q+97 := by omega
  rw [he1,he2] at hp
  exact no_rootFSFE q hp

private theorem no_rootFS (q : Nat) :
    ¬ Reach (10240*q+83) (12288*q+111) := by
  intro hr
  rcases odd_back (10240*q+83) (12288*q+111) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=5120*q+40 := by omega
    have he2 : y=22528*q+194 := by omega
    rw [he1,he2] at hp
    exact no_rootFSF q hp
  · omega

private theorem no_rootF (q : Nat) :
    ¬ Reach (4096*q+35) (24576*q+218) := by
  intro hr
  rcases odd_back (4096*q+35) (24576*q+218) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=2048*q+16 := by omega
    have he2 : y=28672*q+253 := by omega
    rw [he1,he2] at hp
    exact no_rootFF q hp
  · have he1 : x=10240*q+83 := by omega
    have he2 : y=12288*q+111 := by omega
    rw [he1,he2] at hp
    exact no_rootFS q hp

private theorem no_root (q : Nat) :
    ¬ Reach (8192*q+73) (16384*q+145) := by
  intro hr
  rcases odd_back (8192*q+73) (16384*q+145) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=4096*q+35 := by omega
    have he2 : y=24576*q+218 := by omega
    rw [he1,he2] at hp
    exact no_rootF q hp
  · omega

theorem blank_halt_not_73_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192≠73 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+73 := by dsimp [q]; omega
  have hb : b=16384*q+145 := by omega
  have ht : Reach (8192*q+73) (16384*q+145) := by
    exact ⟨n, by simpa only [←ha, ←hb] using hr⟩
  exact no_root q ht

#print axioms blank_halt_not_73_mod8192
end BB429No73

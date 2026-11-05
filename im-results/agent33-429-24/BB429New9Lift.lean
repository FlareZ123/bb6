import BB429NewResidue
import BB429RootMod16
import Lean.Elab.Tactic.Omega

namespace BB429New9Lift
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

private theorem no_2_FSFEFSFEFF (q : Nat) :
    ¬ Reach (2728*q+1360) (27312*q+13645) := by
  intro hr
  have ha := reach_allowed (2728*q+1360) (27312*q+13645) hr
  unfold BB429Mod8.Allowed at ha
  omega
private theorem no_2_FSFEFSFEFS (q : Nat) :
    ¬ Reach (10920*q+5447) (10928*q+5463) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hh := BB429RootMod16.rooted_not_7_7 n (10920*q+5447) (10928*q+5463) hn (by omega)
  omega
private theorem no_2_FSFEFSFEF (q : Nat) :
    ¬ Reach (5456*q+2723) (21856*q+10922) := by
  intro hr
  rcases odd_back (5456*q+2723) (21856*q+10922) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(2728*q+1360) := by omega
    have he2 : y=(27312*q+13645) := by omega
    rw [he1,he2] at hp
    exact no_2_FSFEFSFEFF q hp
  · have he1 : x=(10920*q+5447) := by omega
    have he2 : y=(10928*q+5463) := by omega
    rw [he1,he2] at hp
    exact no_2_FSFEFSFEFS q hp
private theorem no_2_FSFEFSFE (q : Nat) :
    ¬ Reach (10912*q+5449) (10944*q+5473) := by
  intro hr
  rcases odd_back (10912*q+5449) (10944*q+5473) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(5456*q+2723) := by omega
    have he2 : y=(21856*q+10922) := by omega
    rw [he1,he2] at hp
    exact no_2_FSFEFSFEF q hp
  · omega
private theorem no_2_FSFEFSF (q : Nat) :
    ¬ Reach (5440*q+2716) (21888*q+10946) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5440*q+2716) (21888*q+10946)
    (by omega) (by omega) hr
  have he1 : x=(10912*q+5449) := by omega
  have he2 : y=(10944*q+5473) := by omega
  rw [he1,he2] at hp
  exact no_2_FSFEFSFE q hp
private theorem no_2_FSFEFF (q : Nat) :
    ¬ Reach (2688*q+1342) (27392*q+13705) := by
  intro hr
  have ha := reach_allowed (2688*q+1342) (27392*q+13705) hr
  unfold BB429Mod8.Allowed at ha
  omega
private theorem no_2_FSFEFS (q : Nat) :
    ¬ Reach (10880*q+5435) (11008*q+5511) := by
  intro hr
  rcases odd_back (10880*q+5435) (11008*q+5511) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(5440*q+2716) := by omega
    have he2 : y=(21888*q+10946) := by omega
    rw [he1,he2] at hp
    exact no_2_FSFEFSF q hp
  · omega
private theorem no_2_FSFEF (q : Nat) :
    ¬ Reach (5376*q+2687) (22016*q+11018) := by
  intro hr
  rcases odd_back (5376*q+2687) (22016*q+11018) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(2688*q+1342) := by omega
    have he2 : y=(27392*q+13705) := by omega
    rw [he1,he2] at hp
    exact no_2_FSFEFF q hp
  · have he1 : x=(10880*q+5435) := by omega
    have he2 : y=(11008*q+5511) := by omega
    rw [he1,he2] at hp
    exact no_2_FSFEFS q hp
private theorem no_2_FSFE (q : Nat) :
    ¬ Reach (10752*q+5377) (11264*q+5641) := by
  intro hr
  rcases odd_back (10752*q+5377) (11264*q+5641) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(5376*q+2687) := by omega
    have he2 : y=(22016*q+11018) := by omega
    rw [he1,he2] at hp
    exact no_2_FSFEF q hp
  · omega
private theorem no_2_FSF (q : Nat) :
    ¬ Reach (5120*q+2560) (22528*q+11282) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+2560) (22528*q+11282)
    (by omega) (by omega) hr
  have he1 : x=(10752*q+5377) := by omega
  have he2 : y=(11264*q+5641) := by omega
  rw [he1,he2] at hp
  exact no_2_FSFE q hp
private theorem no_2_FF (q : Nat) :
    ¬ Reach (2048*q+1024) (28672*q+14365) := by
  intro hr
  have ha := reach_allowed (2048*q+1024) (28672*q+14365) hr
  unfold BB429Mod8.Allowed at ha
  omega
private theorem no_2_FS (q : Nat) :
    ¬ Reach (10240*q+5123) (12288*q+6159) := by
  intro hr
  rcases odd_back (10240*q+5123) (12288*q+6159) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(5120*q+2560) := by omega
    have he2 : y=(22528*q+11282) := by omega
    rw [he1,he2] at hp
    exact no_2_FSF q hp
  · omega
private theorem no_2_F (q : Nat) :
    ¬ Reach (4096*q+2051) (24576*q+12314) := by
  intro hr
  rcases odd_back (4096*q+2051) (24576*q+12314) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(2048*q+1024) := by omega
    have he2 : y=(28672*q+14365) := by omega
    rw [he1,he2] at hp
    exact no_2_FF q hp
  · have he1 : x=(10240*q+5123) := by omega
    have he2 : y=(12288*q+6159) := by omega
    rw [he1,he2] at hp
    exact no_2_FS q hp

/-- An entire genuine blank-root terminal cylinder excluded by an inverse
    tree of at most ten steps, for every natural parameter. -/
private theorem no_2_ROOT (q : Nat) :
    ¬ Reach (8192*q+4105) (16384*q+8209) := by
  intro hr
  rcases odd_back (8192*q+4105) (16384*q+8209) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(4096*q+2051) := by omega
    have he2 : y=(24576*q+12314) := by omega
    rw [he1,he2] at hp
    exact no_2_F q hp
  · omega
theorem no_halting_2_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192≠4105 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+4105 := by dsimp [q]; omega
  have hb : b=16384*q+8209 := by omega
  have ht : Reach (8192*q+4105) (16384*q+8209) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_2_ROOT q ht

#print axioms no_halting_2_mod8192

private theorem no_3_FSFEFSFEFF (q : Nat) :
    ¬ Reach (2728*q+2042) (27312*q+20473) := by
  intro hr
  have ha := reach_allowed (2728*q+2042) (27312*q+20473) hr
  unfold BB429Mod8.Allowed at ha
  omega
private theorem no_3_FSFEFSFEFS (q : Nat) :
    ¬ Reach (10920*q+8177) (10928*q+8195) := by
  intro hr
  have ha := reach_allowed (10920*q+8177) (10928*q+8195) hr
  unfold BB429Mod8.Allowed at ha
  omega
private theorem no_3_FSFEFSFEF (q : Nat) :
    ¬ Reach (5456*q+4087) (21856*q+16386) := by
  intro hr
  rcases odd_back (5456*q+4087) (21856*q+16386) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(2728*q+2042) := by omega
    have he2 : y=(27312*q+20473) := by omega
    rw [he1,he2] at hp
    exact no_3_FSFEFSFEFF q hp
  · have he1 : x=(10920*q+8177) := by omega
    have he2 : y=(10928*q+8195) := by omega
    rw [he1,he2] at hp
    exact no_3_FSFEFSFEFS q hp
private theorem no_3_FSFEFSFE (q : Nat) :
    ¬ Reach (10912*q+8177) (10944*q+8209) := by
  intro hr
  rcases odd_back (10912*q+8177) (10944*q+8209) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(5456*q+4087) := by omega
    have he2 : y=(21856*q+16386) := by omega
    rw [he1,he2] at hp
    exact no_3_FSFEFSFEF q hp
  · omega
private theorem no_3_FSFEFSF (q : Nat) :
    ¬ Reach (5440*q+4076) (21888*q+16418) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5440*q+4076) (21888*q+16418)
    (by omega) (by omega) hr
  have he1 : x=(10912*q+8177) := by omega
  have he2 : y=(10944*q+8209) := by omega
  rw [he1,he2] at hp
  exact no_3_FSFEFSFE q hp
private theorem no_3_FSFEFF (q : Nat) :
    ¬ Reach (2688*q+2014) (27392*q+20553) := by
  intro hr
  have ha := reach_allowed (2688*q+2014) (27392*q+20553) hr
  unfold BB429Mod8.Allowed at ha
  omega
private theorem no_3_FSFEFS (q : Nat) :
    ¬ Reach (10880*q+8155) (11008*q+8263) := by
  intro hr
  rcases odd_back (10880*q+8155) (11008*q+8263) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(5440*q+4076) := by omega
    have he2 : y=(21888*q+16418) := by omega
    rw [he1,he2] at hp
    exact no_3_FSFEFSF q hp
  · omega
private theorem no_3_FSFEF (q : Nat) :
    ¬ Reach (5376*q+4031) (22016*q+16522) := by
  intro hr
  rcases odd_back (5376*q+4031) (22016*q+16522) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(2688*q+2014) := by omega
    have he2 : y=(27392*q+20553) := by omega
    rw [he1,he2] at hp
    exact no_3_FSFEFF q hp
  · have he1 : x=(10880*q+8155) := by omega
    have he2 : y=(11008*q+8263) := by omega
    rw [he1,he2] at hp
    exact no_3_FSFEFS q hp
private theorem no_3_FSFE (q : Nat) :
    ¬ Reach (10752*q+8065) (11264*q+8457) := by
  intro hr
  rcases odd_back (10752*q+8065) (11264*q+8457) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(5376*q+4031) := by omega
    have he2 : y=(22016*q+16522) := by omega
    rw [he1,he2] at hp
    exact no_3_FSFEF q hp
  · omega
private theorem no_3_FSF (q : Nat) :
    ¬ Reach (5120*q+3840) (22528*q+16914) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hmod⟩ := even_back (5120*q+3840) (22528*q+16914)
    (by omega) (by omega) hr
  have he1 : x=(10752*q+8065) := by omega
  have he2 : y=(11264*q+8457) := by omega
  rw [he1,he2] at hp
  exact no_3_FSFE q hp
private theorem no_3_FF (q : Nat) :
    ¬ Reach (2048*q+1536) (28672*q+21533) := by
  intro hr
  have ha := reach_allowed (2048*q+1536) (28672*q+21533) hr
  unfold BB429Mod8.Allowed at ha
  omega
private theorem no_3_FS (q : Nat) :
    ¬ Reach (10240*q+7683) (12288*q+9231) := by
  intro hr
  rcases odd_back (10240*q+7683) (12288*q+9231) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(5120*q+3840) := by omega
    have he2 : y=(22528*q+16914) := by omega
    rw [he1,he2] at hp
    exact no_3_FSF q hp
  · omega
private theorem no_3_F (q : Nat) :
    ¬ Reach (4096*q+3075) (24576*q+18458) := by
  intro hr
  rcases odd_back (4096*q+3075) (24576*q+18458) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(2048*q+1536) := by omega
    have he2 : y=(28672*q+21533) := by omega
    rw [he1,he2] at hp
    exact no_3_FF q hp
  · have he1 : x=(10240*q+7683) := by omega
    have he2 : y=(12288*q+9231) := by omega
    rw [he1,he2] at hp
    exact no_3_FS q hp

/-- An entire genuine blank-root terminal cylinder excluded by an inverse
    tree of at most ten steps, for every natural parameter. -/
private theorem no_3_ROOT (q : Nat) :
    ¬ Reach (8192*q+6153) (16384*q+12305) := by
  intro hr
  rcases odd_back (8192*q+6153) (16384*q+12305) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(4096*q+3075) := by omega
    have he2 : y=(24576*q+18458) := by omega
    rw [he1,he2] at hp
    exact no_3_F q hp
  · omega
theorem no_halting_3_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192≠6153 := by
  intro hm
  let q := a/8192
  have ha : a=8192*q+6153 := by dsimp [q]; omega
  have hb : b=16384*q+12305 := by omega
  have ht : Reach (8192*q+6153) (16384*q+12305) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_3_ROOT q ht

#print axioms no_halting_3_mod8192

end BB429New9Lift

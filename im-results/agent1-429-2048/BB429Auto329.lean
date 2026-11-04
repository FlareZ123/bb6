import BB429RootMod32
import BB429NewResidue
import Lean.Elab.Tactic.Omega
namespace BB429Auto329
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

private theorem no_329_5 (q : Nat) :
    ¬ Reach (2688*q+421) (2816*q+449) := by
  intro hr
  obtain ⟨n,hn⟩ := hr
  have hi := BB429RootMod32.rooted_not_5_1 n (2688*q+421) (2816*q+449) hn (by omega)
  omega

private theorem no_329_4 (q : Nat) :
    ¬ Reach (1280*q+200) (5632*q+898) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,hw⟩ :=
    even_back (1280*q+200) (5632*q+898) (by omega) (by omega) hr
  have xe : x = 2688*q+421 := by omega
  have ye : y = 2816*q+449 := by omega
  rw [xe,ye] at hp
  exact no_329_5 q hp

private theorem no_329_3 (q : Nat) :
    ¬ Reach (2560*q+403) (3072*q+495) := by
  intro hr
  rcases odd_back (2560*q+403) (3072*q+495) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1280*q+200 := by omega
    have ye : y = 5632*q+898 := by omega
    rw [xe,ye] at hp
    exact no_329_4 q hp
  · omega

private theorem no_329_2 (q : Nat) :
    ¬ Reach (512*q+80) (7168*q+1149) := by
  intro hr
  have ha := reach_allowed (512*q+80) (7168*q+1149) hr
  unfold BB429Mod8.Allowed at ha
  omega

private theorem no_329_1 (q : Nat) :
    ¬ Reach (1024*q+163) (6144*q+986) := by
  intro hr
  rcases odd_back (1024*q+163) (6144*q+986) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 512*q+80 := by omega
    have ye : y = 7168*q+1149 := by omega
    rw [xe,ye] at hp
    exact no_329_2 q hp
  · have xe : x = 2560*q+403 := by omega
    have ye : y = 3072*q+495 := by omega
    rw [xe,ye] at hp
    exact no_329_3 q hp

private theorem no_329_0 (q : Nat) :
    ¬ Reach (2048*q+329) (4096*q+657) := by
  intro hr
  rcases odd_back (2048*q+329) (4096*q+657) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x = 1024*q+163 := by omega
    have ye : y = 6144*q+986 := by omega
    rw [xe,ye] at hp
    exact no_329_1 q hp
  · omega

theorem blank_halt_not_329_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%2048≠329 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+329 := by dsimp [q]; omega
  have hb : b=4096*q+657 := by omega
  have hr0 : Reach (2048*q+329) (4096*q+657) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact no_329_0 q hr0
#print axioms blank_halt_not_329_mod2048
end BB429Auto329

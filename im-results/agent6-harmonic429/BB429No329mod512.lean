import BB429NewResidue
import BB429RootMod32
import Lean.Elab.Tactic.Omega

namespace BB429No329
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
open BB429NewResidue

private theorem no_bad_even_parent (q : Nat) : ¬ Reach (320*q+200) (1408*q+898) := by
  intro hr
  obtain ⟨x,y,hp,hx,hy,_⟩ := even_back (320*q+200) (1408*q+898) (by omega) (by omega) hr
  have hex : x=672*q+421 := by omega
  have hey : y=704*q+449 := by omega
  rw [hex,hey] at hp
  rcases hp with ⟨n,hn⟩
  have he := BB429RootMod32.rooted_not_5_1 n (672*q+421) (704*q+449) hn (by omega)
  exact he (by omega)

private theorem no_bad_odd_parent (q : Nat) : ¬ Reach (640*q+403) (768*q+495) := by
  intro hr
  rcases odd_back (640*q+403) (768*q+495) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hex : x=320*q+200 := by omega
    have hey : y=1408*q+898 := by omega
    rw [hex,hey] at hp
    exact no_bad_even_parent q hp
  · omega

private theorem no_bad_first_parent (q : Nat) : ¬ Reach (256*q+163) (1536*q+986) := by
  intro hr
  rcases odd_back (256*q+163) (1536*q+986) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hex : x=128*q+80 := by omega
    have hey : y=1792*q+1149 := by omega
    rw [hex,hey] at hp
    have ha := reach_allowed (128*q+80) (1792*q+1149) hp
    unfold BB429Mod8.Allowed at ha
    omega
  · have hex : x=640*q+403 := by omega
    have hey : y=768*q+495 := by omega
    rw [hex,hey] at hp
    exact no_bad_odd_parent q hp

private theorem no_329 (q : Nat) : ¬ Reach (512*q+329) (1024*q+657) := by
  intro hr
  rcases odd_back (512*q+329) (1024*q+657) (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hex : x=256*q+163 := by omega
    have hey : y=1536*q+986 := by omega
    rw [hex,hey] at hp
    exact no_bad_first_parent q hp
  · omega

/-- All genuine blank-root halting gateways avoid the complete 329 mod 512 cylinder. -/
theorem blank_halt_not_329_mod512 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) : a%512≠329 := by
  intro hm
  let q := a/512
  have ha : a=512*q+329 := by dsimp [q]; omega
  have hb : b=1024*q+657 := by omega
  have hr2 : Reach (512*q+329) (1024*q+657) := by
    exact ⟨n,by simpa [ha,hb] using hr⟩
  exact no_329 q hr2

#print axioms blank_halt_not_329_mod512
end BB429No329

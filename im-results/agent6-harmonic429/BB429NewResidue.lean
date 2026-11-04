import BB429Mod8
import Lean.Elab.Tactic.Omega
namespace BB429NewResidue
set_option maxHeartbeats 50000000
set_option maxRecDepth 30000

/-- Exhaustive exact inverse of the non-special odd output. -/
theorem odd_inverse (x y a b : Nat)
  (ha : 13≤a) (ho : a%2=1) (hs : BB429.next (x,y)=some (a,b)) :
  (a=2*x+3 ∧ y=b+a) ∨ (4*x+26=4*a+b ∧ 2*y=b+4 ∧ b%4=2) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Exact preimage of a non-special positive even output. -/
theorem even_inverse (x y a b : Nat)
  (ha : 6≤a) (he : a%2=0) (hs : BB429.next (x,y)=some (a,b)) :
  4*x+14=4*a+b ∧ 2*y=b ∧ b%4=2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

def Reach (u w : Nat) : Prop := ∃ n, BB429.run n (0,0)=some (u,w)

theorem pred (a b : Nat) (ha : 0<a) (hr : Reach a b) :
    ∃ x y, Reach x y ∧ BB429.next (x,y)=some (a,b) := by
  rcases hr with ⟨n,hn⟩
  cases n with
  | zero => simp [BB429.run] at hn; omega
  | succ n =>
    simp only [BB429.run] at hn
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hn
    | some p =>
      simp only [hp,Option.bind_some] at hn
      exact ⟨p.1,p.2,⟨n,hp⟩,hn⟩

theorem odd_back (a b : Nat) (ha : 13≤a) (ho : a%2=1) (hr : Reach a b) :
  (∃ x y, Reach x y ∧ a=2*x+3 ∧ y=b+a) ∨
  (∃ x y, Reach x y ∧ 4*x+26=4*a+b ∧ 2*y=b+4 ∧ b%4=2) := by
  obtain ⟨x,y,hp,hs⟩ := pred a b (by omega) hr
  rcases odd_inverse x y a b ha ho hs with h1|h2
  · exact Or.inl ⟨x,y,hp,h1.1,h1.2⟩
  · exact Or.inr ⟨x,y,hp,h2.1,h2.2.1,h2.2.2⟩

theorem even_back (a b : Nat) (ha : 6≤a) (he : a%2=0) (hr : Reach a b) :
  ∃ x y, Reach x y ∧ 4*x+14=4*a+b ∧ 2*y=b ∧ b%4=2 := by
  obtain ⟨x,y,hp,hs⟩ := pred a b (by omega) hr
  obtain ⟨h1,h2,h3⟩ := even_inverse x y a b ha he hs
  exact ⟨x,y,hp,h1,h2,h3⟩

theorem reach_allowed (a b : Nat) (hr : Reach a b) : BB429Mod8.Allowed a b := by
  rcases hr with ⟨n,hn⟩
  exact BB429Mod8.all_blank_returns_allowed n a b hn

private theorem allowed_even_not_three (u w : Nat)
  (h : BB429Mod8.Allowed u w) (hu : u%2=0) (hw : w%4=3) : False := by
  unfold BB429Mod8.Allowed at h
  omega

private theorem no_bad1S (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (10240*q+1280*r+948) (12288*q+1536*r+1149) := by
  intro hr
  have hh := reach_allowed (10240*q+1280*r+948) (12288*q+1536*r+1149) hr
  unfold BB429Mod8.Allowed at hh
  rcases h2345 with h2|h3|h4|h5
  · subst r; omega
  · subst r; omega
  · subst r; omega
  · subst r; omega

private theorem no_bad6F (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (128*q+16*r+9) (32512*q+4064*r+3023) := by
  intro hr
  have hh := reach_allowed (128*q+16*r+9) (32512*q+4064*r+3023) hr
  unfold BB429Mod8.Allowed at hh
  rcases h2345 with h2|h3|h4|h5
  · subst r; omega
  · subst r; omega
  · subst r; omega
  · subst r; omega

private theorem no_bad10F (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (520*q+65*r+45) (31728*q+3966*r+2931) := by
  intro hr
  rcases h2345 with h2|h3|h4|h5
  · subst r
    have hodd := odd_back (520*q+65*2+45) (31728*q+3966*2+2931) (by omega) (by omega) hr
    rcases hodd with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
    · have hex : x=260*q+86 := by omega
      have hey : y=32248*q+11038 := by omega
      rw [hex,hey] at hp
      obtain ⟨xx,yy,hp2,hxx,hyy,hmod⟩ := even_back (260*q+86) (32248*q+11038) (by omega) (by omega) hp
      have hxx2 : xx=8322*q+2842 := by omega
      have hyy2 : yy=16124*q+5519 := by omega
      rw [hxx2,hyy2] at hp2
      have hh := reach_allowed (8322*q+2842) (16124*q+5519) hp2
      exact allowed_even_not_three _ _ hh (by omega) (by omega)
    · omega
  · subst r
    have hh := reach_allowed (520*q+65*3+45) (31728*q+3966*3+2931) hr
    unfold BB429Mod8.Allowed at hh
    omega
  · subst r
    have hh := reach_allowed (520*q+65*4+45) (31728*q+3966*4+2931) hr
    unfold BB429Mod8.Allowed at hh
    omega
  · subst r
    have hh := reach_allowed (520*q+65*5+45) (31728*q+3966*5+2931) hr
    unfold BB429Mod8.Allowed at hh
    omega

private theorem no_bad10S (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (8712*q+1089*r+796) (15344*q+1918*r+1421) := by
  intro hr
  rcases h2345 with h2|h3|h4|h5
  · subst r
    have hh := reach_allowed (8712*q+1089*2+796) (15344*q+1918*2+1421) hr
    unfold BB429Mod8.Allowed at hh
    omega
  · subst r
    have hodd := odd_back (8712*q+1089*3+796) (15344*q+1918*3+1421) (by omega) (by omega) hr
    rcases hodd with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
    · have hex : x=4356*q+2030 := by omega
      have hey : y=24056*q+11238 := by omega
      rw [hex,hey] at hp
      obtain ⟨xx,yy,hp2,hxx,hyy,hmod⟩ := even_back (4356*q+2030) (24056*q+11238) (by omega) (by omega) hp
      have hxx2 : xx=10370*q+4836 := by omega
      have hyy2 : yy=12028*q+5619 := by omega
      rw [hxx2,hyy2] at hp2
      have hh := reach_allowed (10370*q+4836) (12028*q+5619) hp2
      exact allowed_even_not_three _ _ hh (by omega) (by omega)
    · omega
  · subst r
    have hh := reach_allowed (8712*q+1089*4+796) (15344*q+1918*4+1421) hr
    unfold BB429Mod8.Allowed at hh
    omega
  · subst r
    have hh := reach_allowed (8712*q+1089*5+796) (15344*q+1918*5+1421) hr
    unfold BB429Mod8.Allowed at hh
    omega

private theorem no_9 (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (1040*q+130*r+93) (30688*q+3836*r+2838) := by
  intro hr
  have hrp := odd_back (1040*q+130*r+93) (30688*q+3836*r+2838) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(520*q+65*r+45) := by omega
    have he2 : y=(31728*q+3966*r+2931) := by omega
    rw [he1,he2] at hp
    exact no_bad10F q r h2345 hp
  · have he1 : x=(8712*q+1089*r+796) := by omega
    have he2 : y=(15344*q+1918*r+1421) := by omega
    rw [he1,he2] at hp
    exact no_bad10S q r h2345 hp

private theorem no_8 (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (2080*q+260*r+189) (28608*q+3576*r+2649) := by
  intro hr
  have hrp := odd_back (2080*q+260*r+189) (28608*q+3576*r+2649) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(1040*q+130*r+93) := by omega
    have he2 : y=(30688*q+3836*r+2838) := by omega
    rw [he1,he2] at hp
    exact no_9 q r h2345 hp
  · omega

private theorem no_7 (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (4160*q+520*r+381) (24448*q+3056*r+2268) := by
  intro hr
  have hrp := odd_back (4160*q+520*r+381) (24448*q+3056*r+2268) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(2080*q+260*r+189) := by omega
    have he2 : y=(28608*q+3576*r+2649) := by omega
    rw [he1,he2] at hp
    exact no_8 q r h2345 hp
  · omega

private theorem no_6S (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (8320*q+1040*r+765) (16128*q+2016*r+1503) := by
  intro hr
  have hrp := odd_back (8320*q+1040*r+765) (16128*q+2016*r+1503) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(4160*q+520*r+381) := by omega
    have he2 : y=(24448*q+3056*r+2268) := by omega
    rw [he1,he2] at hp
    exact no_7 q r h2345 hp
  · omega

private theorem no_5 (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (256*q+32*r+21) (32256*q+4032*r+3002) := by
  intro hr
  have hrp := odd_back (256*q+32*r+21) (32256*q+4032*r+3002) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(128*q+16*r+9) := by omega
    have he2 : y=(32512*q+4064*r+3023) := by omega
    rw [he1,he2] at hp
    exact no_bad6F q r h2345 hp
  · have he1 : x=(8320*q+1040*r+765) := by omega
    have he2 : y=(16128*q+2016*r+1503) := by omega
    rw [he1,he2] at hp
    exact no_6S q r h2345 hp

private theorem no_4 (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (512*q+64*r+45) (31744*q+3968*r+2957) := by
  intro hr
  have hrp := odd_back (512*q+64*r+45) (31744*q+3968*r+2957) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(256*q+32*r+21) := by omega
    have he2 : y=(32256*q+4032*r+3002) := by omega
    rw [he1,he2] at hp
    exact no_5 q r h2345 hp
  · omega

private theorem no_3 (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (1024*q+128*r+93) (30720*q+3840*r+2864) := by
  intro hr
  have hrp := odd_back (1024*q+128*r+93) (30720*q+3840*r+2864) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(512*q+64*r+45) := by omega
    have he2 : y=(31744*q+3968*r+2957) := by omega
    rw [he1,he2] at hp
    exact no_4 q r h2345 hp
  · omega

private theorem no_2 (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (2048*q+256*r+189) (28672*q+3584*r+2675) := by
  intro hr
  have hrp := odd_back (2048*q+256*r+189) (28672*q+3584*r+2675) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(1024*q+128*r+93) := by omega
    have he2 : y=(30720*q+3840*r+2864) := by omega
    rw [he1,he2] at hp
    exact no_3 q r h2345 hp
  · omega

private theorem no_1 (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (4096*q+512*r+381) (24576*q+3072*r+2294) := by
  intro hr
  have hrp := odd_back (4096*q+512*r+381) (24576*q+3072*r+2294) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(2048*q+256*r+189) := by omega
    have he2 : y=(28672*q+3584*r+2675) := by omega
    rw [he1,he2] at hp
    exact no_2 q r h2345 hp
  · have he1 : x=(10240*q+1280*r+948) := by omega
    have he2 : y=(12288*q+1536*r+1149) := by omega
    rw [he1,he2] at hp
    exact no_bad1S q r h2345 hp

private theorem no_0 (q r : Nat) (h2345 : r=2 ∨ r=3 ∨ r=4 ∨ r=5) :
    ¬ Reach (8192*q+1024*r+765) (16384*q+2048*r+1529) := by
  intro hr
  have hrp := odd_back (8192*q+1024*r+765) (16384*q+2048*r+1529) (by omega) (by omega) hr
  rcases hrp with ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he1 : x=(4096*q+512*r+381) := by omega
    have he2 : y=(24576*q+3072*r+2294) := by omega
    rw [he1,he2] at hp
    exact no_1 q r h2345 hp
  · omega

theorem blank_halt_not_four_residues_mod8192 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%8192≠2813 ∧ a%8192≠3837 ∧ a%8192≠4861 ∧ a%8192≠5885 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hm
    let q := a/8192
    have ha : a=8192*q+2813 := by dsimp [q]; omega
    have hb : b=16384*q+5625 := by omega
    have hr2 : Reach (8192*q+1024*2+765) (16384*q+2048*2+1529) := by
      refine ⟨n,?_⟩
      simpa [show (1024:Nat)*2=2048 by decide,show (2048:Nat)*2=4096 by decide,ha,hb] using hr
    exact (no_0 q 2 (Or.inl rfl)) hr2
  · intro hm
    let q := a/8192
    have ha : a=8192*q+3837 := by dsimp [q]; omega
    have hb : b=16384*q+7673 := by omega
    have hr2 : Reach (8192*q+1024*3+765) (16384*q+2048*3+1529) := by
      refine ⟨n,?_⟩
      simpa [show (1024:Nat)*3=3072 by decide,show (2048:Nat)*3=6144 by decide,ha,hb] using hr
    exact (no_0 q 3 (Or.inr (Or.inl rfl))) hr2
  · intro hm
    let q := a/8192
    have ha : a=8192*q+4861 := by dsimp [q]; omega
    have hb : b=16384*q+9721 := by omega
    have hr2 : Reach (8192*q+1024*4+765) (16384*q+2048*4+1529) := by
      refine ⟨n,?_⟩
      simpa [show (1024:Nat)*4=4096 by decide,show (2048:Nat)*4=8192 by decide,ha,hb] using hr
    exact (no_0 q 4 (Or.inr (Or.inr (Or.inl rfl)))) hr2
  · intro hm
    let q := a/8192
    have ha : a=8192*q+5885 := by dsimp [q]; omega
    have hb : b=16384*q+11769 := by omega
    have hr2 : Reach (8192*q+1024*5+765) (16384*q+2048*5+1529) := by
      refine ⟨n,?_⟩
      simpa [show (1024:Nat)*5=5120 by decide,show (2048:Nat)*5=10240 by decide,ha,hb] using hr
    exact (no_0 q 5 (Or.inr (Or.inr (Or.inr rfl)))) hr2

#print axioms even_inverse
#print axioms odd_inverse
#print axioms blank_halt_not_four_residues_mod8192
end BB429NewResidue

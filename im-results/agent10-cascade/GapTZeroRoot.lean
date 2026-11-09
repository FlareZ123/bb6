import TThreeHighTTwoOne
import GapTZeroGeometry
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeGapTZero
open CascadeSweep CascadeHighTTwo CascadeForkOddDead

/-- Authentic-root exclusion of the no-27 valuation at a 5-mod-6 gap,
    using the exact source first-reset grammar and genuine root obstruction. -/
theorem source_gap_no27_dead
 (n k s g : Nat) (hn:20≤n) (hk:k=n-8) (hs:s=2^k)
 (hsector:n%6=5) (hconst:(8*s+k)%3=1)
 (hlo:9*s+6*k+12<2*g+5)
 (hhi:2*(2*g+5)+12<21*s)
 (h9:(2*g+5)%9=0) (hnot27:(2*g+5)%27≠0) :
 ¬ReachC (2,0) (g,0) := by
  have hgap : 4*2^k<g ∧ 2*g+2<12*2^k := by rw [←hs]; omega
  have hk10 : 10≤k := by omega
  apply generic_gap_no27_root_dead (fun x=>ReachC (2,0) (x,0))
    n k s g hn hk hs hsector hconst hlo hhi h9 hnot27
  · intro hr
    obtain ⟨x,l,t,z,hroot,_,hl,hu,hnum,heq⟩ :=
      gap_root_requires_odd_parent k g hk10 hgap hr
    exact ⟨x,l,t,z,hroot,hl,hu,hnum,heq⟩
  · intro x hxl hxu hxmod
    have hp:2^(k+1)=2*s:=by rw [hs,Nat.pow_succ];omega
    exact root_excludes_nonimage x (by omega)
      (gap_avoids_even_images (k+1) x (by omega)
        (by rw [hp];omega) (by rw [hp];omega))

#print axioms source_gap_no27_dead
end CascadeGapTZero

namespace CascadeGapTZero
open CascadeSweep CascadeHighTTwo CascadeForkOddDead

/-- New genuine-root high-q t=2 restriction: when the two early nine-gates
    fail, any source-rooted four-even chain in the 5-mod-6 sector with its
    fourth ancestor's numerator divisible by nine must pass the 27-gate. -/
theorem four_even_root_forces_twentyseven
 (n s d a b c f g:Nat) (hn:20≤n) (hs:s=2^(n-8))
 (hsector:n%6=5)
 (hdlo:1974*s≤1000*d) (hdhi:1000*d≤1977*s)
 (he0:8*d=8*s+a+(n-8)+5)
 (he1:2*a=8*s+b+(n-8))
 (he2:2*b=8*s+c+(n-8))
 (he3:2*c=8*s+f+(n-8))
 (he4:2*f=8*s+g+(n-8))
 (hdmod:d%3=1)
 (ha9:(2*a+5)%9≠0) (hc9:(2*c+5)%9≠0)
 (hg9:(2*g+5)%9=0)
 (hr:ReachC (2,0) (a,0)) :
 (2*g+5)%27=0 := by
  by_cases h27:(2*g+5)%27=0
  · exact h27
  exfalso
  have hsize:=size200 n hn
  have hgeometry := even_four_geometry n s d a b c f g hn
    (by omega) (by omega) (by omega) he0 he1 he2 he3 he4
  obtain ⟨hbandA,hbandB,hbandC,hbandF,_⟩:=hgeometry
  have hconst:(8*s+(n-8))%3=1:=by
    rw [hs]
    exact even_const_mod_three n hn (Or.inr hsector)
  obtain ⟨_,hbmod,_,hfmod,_⟩:=mod_four_one s (n-8) d a b c f g
    hconst hdmod he0 he1 he2 he3 he4
  have hrG := four_even_one_root_continues (n-8) a b c f g (by omega)
    (by rw [hs] at hbandA; exact hbandA)
    (by rw [hs] at hbandB; exact hbandB)
    (by rw [hs] at hbandC; exact hbandC)
    (by rw [hs] at hbandF; exact hbandF)
    (by rw [hs] at he1; exact he1)
    (by rw [hs] at he2; exact he2)
    (by rw [hs] at he3; exact he3)
    (by rw [hs] at he4; exact he4)
    ha9 hc9 (by omega) (by omega) hr
  obtain ⟨hlo,hhi⟩ := strong_g_corridor n s d a b c f g hn
    (by rw [hs]; exact hsize) hdlo hdhi he0 he1 he2 he3 he4
  exact (source_gap_no27_dead n (n-8) s g hn rfl hs hsector hconst hlo hhi hg9 h27) hrG

#print axioms four_even_root_forces_twentyseven
end CascadeGapTZero

namespace CascadeGapTZero
open CascadeSweep CascadeHighTTwo

/-- In each 5-mod-6 sector, the formerly open mod-nine forced odd fork
    has a new necessary mod-27 numerator condition at its fourth ancestor. -/
theorem forced_d_modnine_requires_g27
 (n s d a b c f g : Nat) (hn:20≤n) (hs:s=2^(n-8))
 (hsector:n%6=5)
 (hdlo:1974*s≤1000*d) (hdhi:1000*d≤1977*s)
 (he0:8*d=8*s+a+(n-8)+5)
 (he1:2*a=8*s+b+(n-8))
 (he2:2*b=8*s+c+(n-8))
 (he3:2*c=8*s+f+(n-8))
 (he4:2*f=8*s+g+(n-8))
 (hforced:(n%18=5 ∧ d%9=1) ∨ (n%18=11 ∧ d%9=4) ∨ (n%18=17 ∧ d%9=7))
 (hroot:ReachC (2,0) (a,0)) :
 (2*g+5)%27=0 := by
  have hk6:(n-8)%6=3:=by omega
  have hs9:s%9=8:=by
    rw [hs,CascadeHighTTwoArithmetic.pow_two_mod_nine]
    simp [hk6]
  have hdmod:d%3=1:=by omega
  have ha9:(2*a+5)%9≠0:=by omega
  have hc9:(2*c+5)%9≠0:=by omega
  have hg9:(2*g+5)%9=0:=by omega
  exact four_even_root_forces_twentyseven n s d a b c f g hn hs hsector
    hdlo hdhi he0 he1 he2 he3 he4 hdmod ha9 hc9 hg9 hroot

#print axioms forced_d_modnine_requires_g27
end CascadeGapTZero

namespace CascadeGapTZero
open CascadeSweep CascadeHighTTwo CascadeTranslatedRayDepth CascadeOddRay

/-- High-q t=2 source-root genuine necessary gate. The previously open
    d mod 9 forced-odd sector at n mod 6 = 5 must lift to mod 27 at g. -/
theorem high_ttwo_one_forced_d_g27
  (n j d0 q e r d a : Nat)
  (hn:20≤n) (hsector:n%6=5)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=81*d0)
  (hrel:16*d0=2^n+q+(n-3)+5)
  (hgate:2*q+5=81*e)
  (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
  (htwo:2*r+5=27*d)
  (he0:8*d=8*2^(n-8)+a+(n-8)+5)
  (hforced:(n%18=5 ∧ d%9=1) ∨ (n%18=11 ∧ d%9=4) ∨ (n%18=17 ∧ d%9=7))
  (hroot:ReachC (2,0) (a,0)) :
  ∃b c f g:Nat,
    2*a=8*2^(n-8)+b+(n-8) ∧
    2*b=8*2^(n-8)+c+(n-8) ∧
    2*c=8*2^(n-8)+f+(n-8) ∧
    2*f=8*2^(n-8)+g+(n-8) ∧
    (2*g+5)%27=0 := by
  obtain ⟨hl,hu⟩ := high_source_ray_bounds n j d0 q e r hn hm hz hrel hgate hrrel
  have hp:2^(n-4)=16*2^(n-8):=by
    have he:n-4=(n-8)+4:=by omega
    rw [he,Nat.pow_add]
    omega
  have hpI:((2^(n-4):Nat):Int)=16*((2^(n-8):Nat):Int):=by exact_mod_cast hp
  have hlI:(10934:Int)*16*((2^(n-8):Nat):Int)-961*(n:Int)+18609≤6561*(r:Int):=by
    rw [hpI] at hl
    simpa only [Int.mul_assoc] using hl
  have huI:(6561:Int)*(r:Int)≤10942*16*((2^(n-8):Nat):Int)-10177*(n:Int)+6321:=by
    rw [hpI] at hu
    simpa only [Int.mul_assoc] using hu
  obtain ⟨hdlo,hdhi⟩ := strong_interval n (2^(n-8)) r d hn (size200 n hn) hlI huI htwo
  have hs64:64*n≤2^(n-8):=by have hs200:=size200 n hn;omega
  obtain ⟨b,c,f,g,he1,he2,he3,he4⟩ := even_four_witnesses n (2^(n-8)) d a hn hs64
    (by omega) (by omega) he0
  have h27 := forced_d_modnine_requires_g27 n (2^(n-8)) d a b c f g hn rfl
    hsector hdlo hdhi he0 he1 he2 he3 he4 hforced hroot
  exact ⟨b,c,f,g,he1,he2,he3,he4,h27⟩

#print axioms high_ttwo_one_forced_d_g27
end CascadeGapTZero

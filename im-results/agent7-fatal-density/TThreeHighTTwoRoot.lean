import TThreeHighOddPrune
import TThreeHighTTwoGeometry
import ForkOddDead27
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeHighTTwo
open CascadeSweep CascadeResetInverse CascadeUniformFatal CascadeForkOddDead

private theorem forced_even_root (k x y:Nat)
  (hx:x≠2)
  (hband:6*2^k-1≤x ∧ x≤8*2^k-3)
  (heq:2*x=8*2^k+y+k)
  (hmod:x%3≠2)
  (hroot:ReachC (2,0) (x,0)) : ReachC (2,0) (y,0) := by
  have hc:ResetChain 2 x := (root_reset_chain_iff x).mp hroot
  obtain ⟨v,hprev,hparent⟩ := reset_chain_last hc hx
  have hv : v=y := any_parent_equals_even x k y v hband heq hmod hparent
  subst v
  exact (root_reset_chain_iff y).mpr hprev

/-- Four exact source first-reset even edges force an ancestor in a true root-forbidden dyadic gap. -/
theorem four_even_root_dead (k a b c f g:Nat) (hk:10≤k)
  (hbandA:6*2^k-1≤a ∧ a≤8*2^k-3)
  (hbandB:6*2^k-1≤b ∧ b≤8*2^k-3)
  (hbandC:6*2^k-1≤c ∧ c≤8*2^k-3)
  (hbandF:6*2^k-1≤f ∧ f≤8*2^k-3)
  (he1:2*a=8*2^k+b+k)
  (he2:2*b=8*2^k+c+k)
  (he3:2*c=8*2^k+f+k)
  (he4:2*f=8*2^k+g+k)
  (ha:a%3≠2) (hb:b%3≠2) (hc:c%3≠2) (hf:f%3≠2)
  (hg:g%3≠2)
  (hgap:4*2^k<g ∧ 2*g+2<12*2^k) :
  ¬ReachC (2,0) (a,0) := by
  have hp:1≤2^k:=Nat.one_le_pow k 2 (by decide)
  have ha2:a≠2:=by omega
  have hb2:b≠2:=by omega
  have hc2:c≠2:=by omega
  have hf2:f≠2:=by omega
  intro hr
  have hbr := forced_even_root k a b ha2 hbandA he1 ha hr
  have hcr := forced_even_root k b c hb2 hbandB he2 hb hbr
  have hfr := forced_even_root k c f hc2 hbandC he3 hc hcr
  have hgr := forced_even_root k f g hf2 hbandF he4 hf hfr
  have hp4 : 2^(k+2)=4*2^k := by rw [Nat.pow_add];omega
  have hgap' : 2^(k+2)<g ∧ 2*g+2<3*2^(k+2) := by
    rw [hp4]
    constructor <;> omega
  exact (root_excludes_nonimage g hg
    (gap_avoids_even_images (k+2) g (by omega) hgap'.1 hgap'.2)) hgr

#print axioms four_even_root_dead
end CascadeHighTTwo

namespace CascadeHighTTwo
open CascadeOddRay CascadeTranslatedRayDepth CascadeSweep

/-- The t=2 first odd predecessor of the second high-q t=3 parent is
    not reachable from the authentic C(2,0) root when its quotient is 2 modulo 3. -/
theorem high_ttwo_quotient_two_root_dead (n j d0 q e r d a:Nat)
  (hn:20≤n) (hsector:n%6=4 ∨ n%6=5)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=81*d0)
  (hrel:16*d0=2^n+q+(n-3)+5)
  (hgate:2*q+5=81*e)
  (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
  (htwo:2*r+5=27*d)
  (he0:8*d=8*2^(n-8)+a+(n-8)+5)
  (hmod:d%3=2) :
  ¬ReachC (2,0) (a,0) := by
  obtain ⟨hl,hu⟩:=high_source_ray_bounds n j d0 q e r hn hm hz hrel hgate hrrel
  obtain ⟨hdlo,hdhi⟩:=high_r_ttwo_interval n r d hn hl hu htwo
  have hs:=size_bound n hn
  obtain ⟨b,c,f,g,he1,he2,he3,he4⟩:=even_four_witnesses n (2^(n-8)) d a
    hn hs hdlo hdhi he0
  obtain ⟨ha,hb,hc,hf,hgap⟩:=even_four_geometry n (2^(n-8)) d a b c f g
    hn hs hdlo hdhi he0 he1 he2 he3 he4
  have hconst:=even_const_mod_three n hn hsector
  obtain ⟨haMod,hbMod,hcMod,hfMod,hgMod⟩:=mod_four (2^(n-8)) (n-8)
    d a b c f g hconst hmod he0 he1 he2 he3 he4
  exact four_even_root_dead (n-8) a b c f g (by omega)
    ha hb hc hf he1 he2 he3 he4
    (by omega) (by omega) (by omega) (by omega) (by omega) hgap

/-- Every true t=2 first-reset odd parent with quotient d mod 3 = 2
    is root-dead, with the dyadic scale derived rather than assumed. -/
theorem high_ttwo_all_scales_quotient_two_root_dead (n j d0 q e r k d a:Nat)
  (hn:20≤n) (hsector:n%6=4 ∨ n%6=5)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=81*d0)
  (hrel:16*d0=2^n+q+(n-3)+5)
  (hgate:2*q+5=81*e)
  (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
  (htwo:2*r+5=27*d)
  (hband:6*2^k+1≤4*d ∧ 4*d≤8*2^k-1)
  (he0:8*d=8*2^k+a+k+5)
  (hdmod:d%3=2) : ¬ReachC (2,0) (a,0) := by
  obtain ⟨hl,hu⟩:=high_source_ray_bounds n j d0 q e r hn hm hz hrel hgate hrrel
  obtain ⟨hdlo,hdhi⟩:=high_r_ttwo_interval n r d hn hl hu htwo
  have hb:=t_two_image_band n d hn hdlo hdhi
  have hk:k=n-8:=odd_band_scale_unique (4*d) k (n-8) hband hb
  subst k
  exact high_ttwo_quotient_two_root_dead n j d0 q e r d a hn hsector
    hm hz hrel hgate hrrel htwo he0 hdmod

/-- Complete original-source rooted predecessor restriction for high-q:
    t=0,1 are absent; t=2 with quotient 2 modulo 3 cannot be rooted. -/
theorem high_rooted_parent_ttwo_prune (n j d0 q e r a:Nat)
  (hn:20≤n) (hsector:n%6=4 ∨ n%6=5)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=81*d0)
  (hrel:16*d0=2^n+q+(n-3)+5)
  (hgate:2*q+5=81*e)
  (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
  (hroot:ReachC (2,0) (a,0))
  (hparent:CascadeResetInverse.ResetParent a r) :
    (∃k,(6*2^k-1≤r ∧ r≤8*2^k-3) ∧ 2*r=8*2^k+a+k) ∨
    (∃k t d,2≤t ∧ (t=2 → d%3≠2) ∧ d%2=1 ∧
      (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
      2*r+5=3^(t+1)*d ∧ 2*(2^t*d)=8*2^k+a+k+5) := by
  rcases high_source_parent_low_odd_prune n j d0 q e r a hn hm hz hrel hgate
      hrrel hparent with hev | ⟨k,t,d,ht,hd,hband,hnum,heq⟩
  · exact Or.inl hev
  · refine Or.inr ⟨k,t,d,ht,?_,hd,hband,hnum,heq⟩
    intro ht2 hd2
    subst t
    have hnum2 : 2*r+5=27*d := by simpa using hnum
    have he2 : 8*d=8*2^k+a+k+5 := by omega
    exact (high_ttwo_all_scales_quotient_two_root_dead n j d0 q e r k d a
      hn hsector hm hz hrel hgate hrrel hnum2 (by simpa using hband)
      he2 hd2) hroot

#print axioms high_ttwo_quotient_two_root_dead
#print axioms high_ttwo_all_scales_quotient_two_root_dead
#print axioms high_rooted_parent_ttwo_prune
end CascadeHighTTwo

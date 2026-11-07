import TThreeHighTTwoRoot
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeHighTTwo

theorem f_tone_gap (n s d a b c f g z:Nat)
 (hn:20≤n) (hs:64*n≤s)
 (hdlo:1973*s≤1000*d) (hdhi:1000*d≤1979*s)
 (he0:8*d=8*s+a+(n-8)+5)
 (he1:2*a=8*s+b+(n-8))
 (he2:2*b=8*s+c+(n-8))
 (he3:2*c=8*s+f+(n-8))
 (he4:2*f=8*s+g+(n-8))
 (hz:2*f+5=9*z):
 2*s<2*z ∧ 2*(2*z)+2<6*s := by
 have hk:n-8+8=n:=by omega
 constructor <;> omega

theorem mod_four_zero (s k d a b c f g:Nat)
 (hconst:(8*s+k)%3=1) (hd:d%3=0)
 (h0:8*d=8*s+a+k+5)
 (h1:2*a=8*s+b+k)
 (h2:2*b=8*s+c+k)
 (h3:2*c=8*s+f+k)
 (h4:2*f=8*s+g+k):
 a%3=0 ∧ b%3=2 ∧ c%3=0 ∧ f%3=2 ∧ g%3=0 := by
 constructor
 · omega
 constructor
 · omega
 constructor
 · omega
 constructor
 · omega
 · omega
#print axioms f_tone_gap
#print axioms mod_four_zero
end CascadeHighTTwo

namespace CascadeHighTTwo
open CascadeSweep CascadeResetInverse CascadeUniformFatal CascadeForkOddDead CascadeForkOddDead27

private theorem even_band_tzero_gap (k h z:Nat)
 (hk:1≤k)
 (hband:6*2^k-1≤h ∧ h≤8*2^k-3)
 (hz:2*h+5=3*z):
 4*2^k<z ∧ 2*z+2<12*2^k := by
 have hp:2≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hk
 constructor <;> omega

/-- Exact even-band targets with 2h+5 not divisible by nine have a unique even reset predecessor. -/
theorem band_nonine_parent_even (k h w a:Nat)
 (hk:1≤k)
 (hband:6*2^k-1≤h ∧ h≤8*2^k-3)
 (he:2*h=8*2^k+w+k)
 (hnot9:(2*h+5)%9≠0)
 (hparent:ResetParent a h):a=w:=by
 rcases hparent with ⟨k',hb,heq⟩|⟨k',t,d,hd,hb,hnum,heq⟩
 · have hk:k'=k:=even_band_scale_unique h k' k hb hband
   rw[hk] at heq
   omega
 · by_cases ht:t=0
   · subst t
     have hz:2*h+5=3*d:=by simpa using hnum
     have hgap:=even_band_tzero_gap k h d hk hband hz
     have hpow:2^(k+2)=4*2^k:=by rw[Nat.pow_add];omega
     have hg:2^(k+2)<d ∧ 2*d+2<3*2^(k+2):=by rw[hpow];constructor <;> omega
     have hbad:¬(6*2^k'+1≤d ∧ d≤8*2^k'-1):=
       CascadeForkOddDead27.gap_avoids_odd_images (k+2) d hg.1 hg.2 k'
     exact False.elim (hbad (by simpa using hb))
   · have ht1:1≤t:=by omega
     have hpow:3^(t+1)%9=0:=by
       have heq:t+1=2+(t-1):=by omega
       rw[heq,Nat.pow_add]
       simp
     have hdiv:(2*h+5)%9=0:=by rw[hnum,Nat.mul_mod,hpow];simp
     exact False.elim (hnot9 hdiv)

/-- Only the even parent of f survives when 2f+5 is not divisible by 27. -/
theorem band_f_no27_parent_even (k f w a:Nat)
 (hk:1≤k)
 (hband:6*2^k-1≤f ∧ f≤8*2^k-3)
 (he:2*f=8*2^k+w+k)
 (htone:∀z,2*f+5=9*z→2*2^k<2*z ∧ 2*(2*z)+2<6*2^k)
 (hnot27:(2*f+5)%27≠0)
 (hparent:ResetParent a f):a=w:=by
 rcases hparent with ⟨k',hb,heq⟩|⟨k',t,d,hd,hb,hnum,heq⟩
 · have hk:k'=k:=even_band_scale_unique f k' k hb hband
   rw[hk] at heq
   omega
 · by_cases ht0:t=0
   · subst t
     have hz:2*f+5=3*d:=by simpa using hnum
     have hgap:=even_band_tzero_gap k f d hk hband hz
     have hpow:2^(k+2)=4*2^k:=by rw[Nat.pow_add];omega
     have hg:2^(k+2)<d ∧ 2*d+2<3*2^(k+2):=by rw[hpow];constructor <;> omega
     exact False.elim ((CascadeForkOddDead27.gap_avoids_odd_images (k+2) d hg.1 hg.2)
       k' (by simpa using hb))
   · by_cases ht1:t=1
     · subst t
       have hz:2*f+5=9*d:=by simpa using hnum
       have hgap:=htone d hz
       have hpow:2^(k+1)=2*2^k:=by rw[Nat.pow_succ];omega
       have hg:2^(k+1)<2*d ∧ 2*(2*d)+2<3*2^(k+1):=by rw[hpow];constructor <;> omega
       exact False.elim ((CascadeForkOddDead27.gap_avoids_odd_images (k+1) (2*d) hg.1 hg.2)
         k' (by simpa using hb))
     · have ht2:2≤t:=by omega
       have hpow:3^(t+1)%27=0:=by
         have heq:t+1=3+(t-2):=by omega
         rw[heq,Nat.pow_add]
         simp
       have hdiv:(2*f+5)%27=0:=by rw[hnum,Nat.mul_mod,hpow];simp
       exact False.elim (hnot27 hdiv)

#print axioms band_nonine_parent_even
#print axioms band_f_no27_parent_even
end CascadeHighTTwo

namespace CascadeHighTTwo
open CascadeSweep CascadeResetInverse CascadeUniformFatal CascadeForkOddDead

private theorem forced_parent_root (x y:Nat) (hx:x≠2)
 (hun:∀a,ResetParent a x→a=y)
 (hroot:ReachC (2,0) (x,0)):
 ReachC (2,0) (y,0) := by
 have hc:ResetChain 2 x:=(root_reset_chain_iff x).mp hroot
 obtain ⟨v,hchain,hv⟩:=reset_chain_last hc hx
 have hxy:v=y:=hun v hv
 subst v
 exact (root_reset_chain_iff y).mpr hchain

/-- Missing both higher odd gates forces four even steps into a root-forbidden gap. -/
theorem four_even_zero_root_dead (k a b c f g:Nat) (hk:10≤k)
  (hbandA:6*2^k-1≤a ∧ a≤8*2^k-3)
  (hbandB:6*2^k-1≤b ∧ b≤8*2^k-3)
  (hbandC:6*2^k-1≤c ∧ c≤8*2^k-3)
  (hbandF:6*2^k-1≤f ∧ f≤8*2^k-3)
  (he1:2*a=8*2^k+b+k)
  (he2:2*b=8*2^k+c+k)
  (he3:2*c=8*2^k+f+k)
  (he4:2*f=8*2^k+g+k)
  (hamod:a%3=0) (hcmod:c%3=0) (hgmod:g%3=0)
  (hnot9:(2*b+5)%9≠0) (hnot27:(2*f+5)%27≠0)
  (htone:∀z,2*f+5=9*z→2*2^k<2*z ∧ 2*(2*z)+2<6*2^k)
  (hgap:4*2^k<g ∧ 2*g+2<12*2^k):
  ¬ReachC (2,0) (a,0) := by
 have hp:1≤2^k:=Nat.one_le_pow k 2 (by decide)
 have ha2:a≠2:=by omega
 have hb2:b≠2:=by omega
 have hc2:c≠2:=by omega
 have hf2:f≠2:=by omega
 intro hr
 have hbr:ReachC (2,0) (b,0) := forced_parent_root a b ha2
   (fun w hw=>any_parent_equals_even a k b w hbandA he1 (by omega) hw) hr
 have hcr:ReachC (2,0) (c,0) := forced_parent_root b c hb2
   (fun w hw=>band_nonine_parent_even k b c w (by omega) hbandB he2 hnot9 hw) hbr
 have hfr:ReachC (2,0) (f,0) := forced_parent_root c f hc2
   (fun w hw=>any_parent_equals_even c k f w hbandC he3 (by omega) hw) hcr
 have hgr:ReachC (2,0) (g,0) := forced_parent_root f g hf2
   (fun w hw=>band_f_no27_parent_even k f g w (by omega) hbandF he4 htone hnot27 hw) hfr
 have hpow:2^(k+2)=4*2^k:=by rw[Nat.pow_add];omega
 have hgap':2^(k+2)<g ∧ 2*g+2<3*2^(k+2):=by rw[hpow];constructor <;> omega
 exact (root_excludes_nonimage g (by omega)
   (gap_avoids_even_images (k+2) g (by omega) hgap'.1 hgap'.2)) hgr

#print axioms four_even_zero_root_dead
end CascadeHighTTwo

namespace CascadeHighTTwo
open CascadeSweep CascadeResetInverse CascadeUniformFatal CascadeForkOddDead CascadeOddRay CascadeTranslatedRayDepth

/-- When d%3=0, a genuine rooted t=2 arm requires a /9 gate at b or a /27 gate at f. -/
theorem ttwo_zero_two_gates (n j d0 q e r d a:Nat)
 (hn:20≤n) (hsector:n%6=4∨n%6=5)
 (hm:2048*deficit n j+16384*n+16384≤2^n)
 (hz:2*ray n j+5=81*d0)
 (hrel:16*d0=2^n+q+(n-3)+5)
 (hgate:2*q+5=81*e)
 (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
 (htwo:2*r+5=27*d)
 (he0:8*d=8*2^(n-8)+a+(n-8)+5)
 (hdmod:d%3=0)
 (hroot:ReachC (2,0) (a,0)) :
 ∃b c f g:Nat,
   2*a=8*2^(n-8)+b+(n-8) ∧
   2*b=8*2^(n-8)+c+(n-8) ∧
   2*c=8*2^(n-8)+f+(n-8) ∧
   2*f=8*2^(n-8)+g+(n-8) ∧
   ((2*b+5)%9=0 ∨ (2*f+5)%27=0) := by
 obtain ⟨hl,hu⟩:=CascadeTranslatedRayDepth.high_source_ray_bounds n j d0 q e r hn hm hz hrel hgate hrrel
 obtain ⟨hdlo,hdhi⟩:=high_r_ttwo_interval n r d hn hl hu htwo
 have hs:=size_bound n hn
 obtain ⟨b,c,f,g,he1,he2,he3,he4⟩:=even_four_witnesses n (2^(n-8)) d a
     hn hs hdlo hdhi he0
 refine ⟨b,c,f,g,he1,he2,he3,he4,?_⟩
 by_cases hb9:(2*b+5)%9=0
 · exact Or.inl hb9
 by_cases hf27:(2*f+5)%27=0
 · exact Or.inr hf27
 exfalso
 obtain ⟨ha,hb,hc,hf,hgap⟩:=even_four_geometry n (2^(n-8)) d a b c f g
     hn hs hdlo hdhi he0 he1 he2 he3 he4
 have hconst:=even_const_mod_three n hn hsector
 obtain ⟨haMod,hbMod,hcMod,hfMod,hgMod⟩:=mod_four_zero (2^(n-8)) (n-8)
     d a b c f g hconst hdmod he0 he1 he2 he3 he4
 have htone:∀z,2*f+5=9*z→2*2^(n-8)<2*z ∧ 2*(2*z)+2<6*2^(n-8) := by
   intro z hz
   exact f_tone_gap n (2^(n-8)) d a b c f g z hn hs hdlo hdhi
       he0 he1 he2 he3 he4 hz
 have hdead := four_even_zero_root_dead (n-8) a b c f g (by omega)
   ha hb hc hf he1 he2 he3 he4 haMod hcMod hgMod hb9 hf27 htone hgap
 exact hdead hroot

#print axioms ttwo_zero_two_gates
end CascadeHighTTwo


namespace CascadeHighTTwo
/-- Divisibility of the first t=2 quotient by nine excludes both residual low-valuation odd gates. -/
theorem nine_gate_failure (s k d a b c f g:Nat)
 (hconst:(8*s+k)%3=1) (hd:d%9=0)
 (h0:8*d=8*s+a+k+5)
 (h1:2*a=8*s+b+k)
 (h2:2*b=8*s+c+k)
 (h3:2*c=8*s+f+k)
 (_h4:2*f=8*s+g+k):
 (2*b+5)%9≠0 ∧ (2*f+5)%27≠0 := by
  constructor <;> omega

/-- A genuine t=2 high-q predecessor whose quotient is 0 modulo nine is unreachable from blank. -/
theorem high_ttwo_nine_zero_root_dead (n j d0 q e r d a:Nat)
 (hn:20≤n) (hsector:n%6=4∨n%6=5)
 (hm:2048*CascadeOddRay.deficit n j+16384*n+16384≤2^n)
 (hz:2*CascadeOddRay.ray n j+5=81*d0)
 (hrel:16*d0=2^n+q+(n-3)+5)
 (hgate:2*q+5=81*e)
 (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
 (htwo:2*r+5=27*d)
 (he0:8*d=8*2^(n-8)+a+(n-8)+5)
 (hdmod:d%9=0) :
 ¬CascadeSweep.ReachC (2,0) (a,0) := by
  intro hroot
  have hd3:d%3=0:=by omega
  obtain ⟨b,c,f,g,h1,h2,h3,h4,hdisj⟩ := ttwo_zero_two_gates n j d0 q e r d a
    hn hsector hm hz hrel hgate hrrel htwo he0 hd3 hroot
  have hconst:=even_const_mod_three n hn hsector
  obtain ⟨hbnot,hfnot⟩ := nine_gate_failure (2^(n-8)) (n-8) d a b c f g
    hconst hdmod he0 h1 h2 h3 h4
  exact hdisj.elim (fun h => hbnot h) (fun h => hfnot h)

#print axioms nine_gate_failure
#print axioms high_ttwo_nine_zero_root_dead
end CascadeHighTTwo


namespace CascadeHighTTwo
/-- In the exact source t=2 odd predecessor branch, any image scale is forced to n-8; divisible-by-nine quotients are root-dead. -/
theorem high_ttwo_nine_zero_all_scales (n j d0 q e r k d a:Nat)
 (hn:20≤n) (hsector:n%6=4∨n%6=5)
 (hm:2048*CascadeOddRay.deficit n j+16384*n+16384≤2^n)
 (hz:2*CascadeOddRay.ray n j+5=81*d0)
 (hrel:16*d0=2^n+q+(n-3)+5)
 (hgate:2*q+5=81*e)
 (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
 (htwo:2*r+5=27*d)
 (hband:6*2^k+1≤4*d ∧ 4*d≤8*2^k-1)
 (he0:8*d=8*2^k+a+k+5)
 (hdmod:d%9=0) :
 ¬CascadeSweep.ReachC (2,0) (a,0) := by
  obtain ⟨hl,hu⟩:=CascadeTranslatedRayDepth.high_source_ray_bounds n j d0 q e r hn hm hz hrel hgate hrrel
  obtain ⟨hdlo,hdhi⟩:=high_r_ttwo_interval n r d hn hl hu htwo
  have hbandReal:=t_two_image_band n d hn hdlo hdhi
  have hk:k=n-8:=odd_band_scale_unique (4*d) k (n-8) hband hbandReal
  subst k
  exact high_ttwo_nine_zero_root_dead n j d0 q e r d a hn hsector
    hm hz hrel hgate hrrel htwo he0 hdmod

/-- At arbitrary exact t=2 dyadic scale, the quotient-zero residue requires a secondary /9 or /27 gate. -/
theorem high_ttwo_zero_two_gates_all_scales (n j d0 q e r k d a:Nat)
 (hn:20≤n) (hsector:n%6=4∨n%6=5)
 (hm:2048*CascadeOddRay.deficit n j+16384*n+16384≤2^n)
 (hz:2*CascadeOddRay.ray n j+5=81*d0)
 (hrel:16*d0=2^n+q+(n-3)+5)
 (hgate:2*q+5=81*e)
 (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
 (htwo:2*r+5=27*d)
 (hband:6*2^k+1≤4*d ∧ 4*d≤8*2^k-1)
 (he0:8*d=8*2^k+a+k+5)
 (hdmod:d%3=0)
 (hroot:CascadeSweep.ReachC (2,0) (a,0)) :
 ∃b c f g:Nat,
   2*a=8*2^(n-8)+b+(n-8) ∧
   2*b=8*2^(n-8)+c+(n-8) ∧
   2*c=8*2^(n-8)+f+(n-8) ∧
   2*f=8*2^(n-8)+g+(n-8) ∧
   ((2*b+5)%9=0 ∨ (2*f+5)%27=0) := by
  obtain ⟨hl,hu⟩:=CascadeTranslatedRayDepth.high_source_ray_bounds n j d0 q e r hn hm hz hrel hgate hrrel
  obtain ⟨hdlo,hdhi⟩:=high_r_ttwo_interval n r d hn hl hu htwo
  have hbandReal:=t_two_image_band n d hn hdlo hdhi
  have hk:k=n-8:=odd_band_scale_unique (4*d) k (n-8) hband hbandReal
  subst k
  exact ttwo_zero_two_gates n j d0 q e r d a hn hsector hm hz hrel hgate
    hrrel htwo he0 hdmod hroot

#print axioms high_ttwo_nine_zero_all_scales
#print axioms high_ttwo_zero_two_gates_all_scales
end CascadeHighTTwo


namespace CascadeHighTTwo

/-- Source-root necessary condition for quotients 3 modulo 9: the fourth even ancestor passes the /27 gate. -/
theorem high_ttwo_three_requires_f27 (n j d0 q e r d a:Nat)
 (hn:20≤n) (hsector:n%6=4∨n%6=5)
 (hm:2048*CascadeOddRay.deficit n j+16384*n+16384≤2^n)
 (hz:2*CascadeOddRay.ray n j+5=81*d0)
 (hrel:16*d0=2^n+q+(n-3)+5)
 (hgate:2*q+5=81*e)
 (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
 (htwo:2*r+5=27*d)
 (he0:8*d=8*2^(n-8)+a+(n-8)+5)
 (hdmod:d%9=3)
 (hroot:CascadeSweep.ReachC (2,0) (a,0)):
 ∃b c f g:Nat,
   2*a=8*2^(n-8)+b+(n-8) ∧
   2*b=8*2^(n-8)+c+(n-8) ∧
   2*c=8*2^(n-8)+f+(n-8) ∧
   2*f=8*2^(n-8)+g+(n-8) ∧
   (2*f+5)%27=0 := by
  have hd3:d%3=0:=by omega
  obtain ⟨b,c,f,g,h1,h2,h3,h4,hdisj⟩ := ttwo_zero_two_gates n j d0 q e r d a
      hn hsector hm hz hrel hgate hrrel htwo he0 hd3 hroot
  refine ⟨b,c,f,g,h1,h2,h3,h4,?_⟩
  have hconst:=even_const_mod_three n hn hsector
  have hbnot:(2*b+5)%9≠0:=by omega
  exact hdisj.elim (fun h => (hbnot h).elim) id

/-- Two dyadic ancestor gates rewritten as one quotient congruence. -/
theorem two_gate_mod27_normal_form (K d a b c f:Nat)
 (hconst:K%3=1) (hd:d%3=0)
 (h0:8*d=K+a+5) (h1:2*a=K+b) (h2:2*b=K+c) (h3:2*c=K+f)
 (hg:(2*b+5)%9=0 ∨ (2*f+5)%27=0) :
 d%9=6 ∨ (128*d)%27=(30*K+75)%27 := by
  rcases hg with hb|hf
  · left; omega
  · right; omega

/-- Rooted t=2 quotient-zero branch occupies only the 6 mod9 class or one indexed residue class modulo 27. -/
theorem high_ttwo_zero_quotient_residue (n j d0 q e r d a:Nat)
 (hn:20≤n) (hsector:n%6=4∨n%6=5)
 (hm:2048*CascadeOddRay.deficit n j+16384*n+16384≤2^n)
 (hz:2*CascadeOddRay.ray n j+5=81*d0)
 (hrel:16*d0=2^n+q+(n-3)+5)
 (hgate:2*q+5=81*e)
 (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
 (htwo:2*r+5=27*d)
 (he0:8*d=8*2^(n-8)+a+(n-8)+5)
 (hdmod:d%3=0)
 (hroot:CascadeSweep.ReachC (2,0) (a,0)):
 d%9=6 ∨ (128*d)%27=(30*(8*2^(n-8)+(n-8))+75)%27 := by
  obtain ⟨b,c,f,g,h1,h2,h3,h4,hg⟩ := ttwo_zero_two_gates n j d0 q e r d a
    hn hsector hm hz hrel hgate hrrel htwo he0 hdmod hroot
  have hconst:=even_const_mod_three n hn hsector
  exact two_gate_mod27_normal_form (8*2^(n-8)+(n-8)) d a b c f
    hconst hdmod
    (by calc
      8*d = 8*2^(n-8)+a+(n-8)+5 := he0
      _ = (8*2^(n-8)+(n-8))+a+5 := by ac_rfl)
    (by calc
      2*a = 8*2^(n-8)+b+(n-8) := h1
      _ = (8*2^(n-8)+(n-8))+b := by ac_rfl)
    (by calc
      2*b = 8*2^(n-8)+c+(n-8) := h2
      _ = (8*2^(n-8)+(n-8))+c := by ac_rfl)
    (by calc
      2*c = 8*2^(n-8)+f+(n-8) := h3
      _ = (8*2^(n-8)+(n-8))+f := by ac_rfl) hg

#print axioms high_ttwo_three_requires_f27
#print axioms two_gate_mod27_normal_form
#print axioms high_ttwo_zero_quotient_residue
end CascadeHighTTwo

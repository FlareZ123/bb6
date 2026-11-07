import TThreeHighTTwoResidues
set_option maxHeartbeats 0
namespace CascadeHighTTwo
open CascadeOddRay CascadeSweep CascadeTranslatedRayDepth

/-- Necessary residue selector for every authentic blank-rooted t=2 odd inverse arm of the high-q second t=3 child. Exactly 13 of 27 quotient classes remain formally possible for each surviving n%18 sector. All nine d%3=2 classes and five of nine d%3=0 classes are source-root dead. No sufficiency is claimed. -/
theorem rooted_ttwo_13_mod27_selector (n j d0 q e r k d a:Nat)
 (hn:20≤n) (hsector:n%6=4∨n%6=5)
 (hm:2048*deficit n j+16384*n+16384≤2^n)
 (hz:2*ray n j+5=81*d0)
 (hrel:16*d0=2^n+q+(n-3)+5)
 (hgate:2*q+5=81*e)
 (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
 (htwo:2*r+5=27*d)
 (hband:6*2^k+1≤4*d ∧ 4*d≤8*2^k-1)
 (he0:8*d=8*2^k+a+k+5)
 (hroot:ReachC (2,0) (a,0)) :
 d%3=1 ∨ d%9=6 ∨
 (((n%18=4∨n%18=17)∧d%27=12) ∨
  ((n%18=5∨n%18=10)∧d%27=21) ∨
  ((n%18=11∨n%18=16)∧d%27=3)) := by
  by_cases hd0:d%3=0
  · obtain ⟨hl,hu⟩ := high_source_ray_bounds n j d0 q e r hn hm hz hrel hgate hrrel
    obtain ⟨hlo,hhi⟩ := high_r_ttwo_interval n r d hn hl hu htwo
    have hbandReal := t_two_image_band n d hn hlo hhi
    have hk:k=n-8:=odd_band_scale_unique (4*d) k (n-8) hband hbandReal
    subst k
    have hg := high_ttwo_zero_period18_gate n j d0 q e r d a hn hsector hm hz hrel hgate hrrel htwo he0 hd0 hroot
    rcases hg with h6|hr
    · exact Or.inr (Or.inl h6)
    · exact Or.inr (Or.inr hr)
  · by_cases hd2:d%3=2
    · exact False.elim ((high_ttwo_all_scales_quotient_two_root_dead n j d0 q e r k d a hn hsector hm hz hrel hgate hrrel htwo hband he0 hd2) hroot)
    · exact Or.inl (by omega)

#print axioms rooted_ttwo_13_mod27_selector
end CascadeHighTTwo

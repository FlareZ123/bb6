import EvenWalkSourceModel
import RayTwoGateExact
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace GapNumber
private theorem odd_band_unique (u k l:Nat)
  (hk:6*2^k+1≤u ∧ u≤8*2^k-1)
  (hl:6*2^l+1≤u ∧ u≤8*2^l-1):k=l:=by
  by_cases he:k=l
  · exact he
  by_cases hklt:k<l
  · have hp:2^(k+1)≤2^l:=
      Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega
  · have hp:2^(l+1)≤2^k:=
      Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega

private theorem power16 (n:Nat) (hn:25≤n): 2^n=16*2^(n-4):=by
  have he:n=(n-4)+4:=by omega
  rw[he,Nat.pow_add]
  simp [Nat.mul_comm]

/-- Uniform actual blank-root exclusion for second-tier low-valuation
    off-ray forks. Every source-possible scale and odd return witness is
    retained until the exact dyadic band proves its unique scale. -/
theorem offray_tone_low_two_root_dead (n j h w:Nat) (hn:25≤n)
 (hsector:n%6=4 ∨ n%6=5)
 (hm:32*CascadeOddRay.deficit n j+64*n+128≤2^n)
 (hl:9*h+8*CascadeOddRay.deficit n j+9*n+7=14*2^n)
 (he:2*h=2*2^n+w+(n-2))
 (hdiv:(2*h+5)%27≠0) (wdiv:(2*w+5)%27≠0) :
 ¬CascadeSweep.ReachC (2,0) (h,0):=by
 intro hr
 obtain ⟨q,k,d,hqr,hdodd,hband,hw,hq⟩:=
   (CascadeRayTwoGate.offray_fork_root_iff_second_tone
     n (CascadeOddRay.deficit n j) h w (by omega) hm hl he hdiv wdiv).mp hr
 have hgeometry:=CascadeRayOddStrip.ray_offfork_geometry n
   (CascadeOddRay.deficit n j) h w (by omega) hm hl he
 have hlow:2^n<w:=hgeometry.2.2.2.1
 have hupper:8*w+32<9*2^n:=by omega
 have hscale:=power16 n hn
 have hband0:6*2^(n-4)+1≤2*d ∧ 2*d≤8*2^(n-4)-1:=by
   rw[hscale] at hlow hupper
   omega
 have hk:k=n-4:=odd_band_unique (2*d) k (n-4) hband hband0
 rw[hk] at hq
 have hdclosed:CascadeOddRay.deficit n j+(n-1)=2^j*(2*n+3):=
   CascadeOddRay.deficit_closed n j (by omega)
 exact (second_tier_root_dead n j (CascadeOddRay.deficit n j) h w q d hn
   hsector hdclosed hm hl he hw wdiv hband0 hq) hqr

#print axioms offray_tone_low_two_root_dead
end GapNumber

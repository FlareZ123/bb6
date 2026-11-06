import PacketSelector
import ForkOddDead
set_option maxHeartbeats 0
namespace CascadeRayForkPrune
open CascadeOddRay CascadeRayPeriod CascadeFiveForced CascadeResetInverse

private theorem power_halve2 (n:Nat) (hn:4≤n):
    2^n=4*2^(n-2):=by
  have he:n=(n-2)+2:=by omega
  calc
    2^n=2^((n-2)+2):=congrArg (fun t:Nat=>2^t) he
    _ =4*2^(n-2):=by rw [Nat.pow_add];omega

private theorem pow_mod3 (n:Nat):
    2^n%3=if n%2=0 then 1 else 2:=by
  induction n with
  | zero=>decide
  | succ n ih=>
    rw [Nat.pow_succ,Nat.mul_mod,ih]
    by_cases hp:n%2=0
    · simp [hp]
      omega
    · have hp1:n%2=1:=by omega
      simp [hp1]
      omega

private theorem pow_matches_index (n:Nat)
    (hsector:n%6=4∨n%6=5): 2^n%3=n%3:=by
  rw [pow_mod3]
  rcases hsector with h|h
  · have hp:n%2=0:=by omega
    simp [hp]
    omega
  · have hp:n%2=1:=by omega
    simp [hp]
    omega

/-- General root pruning for a valuation-one odd fork at an arbitrary
    near-top even-ray depth. Input d is the exact quotient Z/9 and q is the
    t=1 odd predecessor (the equation matches source k=n-2). If q%3=1,
    its only possible prior reset lies in a source-forbidden dyadic gap. -/
theorem odd_tone_parent_unreachable (n j q d:Nat) (hn:4≤n)
    (hsector:n%6=4∨n%6=5)
    (hmargin:16*deficit n j+27*n+16≤2^n)
    (hd:9*d+2*deficit n j=8*2^n+5)
    (hq:q+2*2^n+n+3=4*d)
    (hmod:q%3=1):
    ¬CascadeSweep.ReachC (2,0) (q,0):=by
  intro hr
  have hp:=power_halve2 n hn
  have hband:6*2^(n-2)-1≤q∧q≤8*2^(n-2)-3:=by
    omega
  obtain ⟨h,k,hreach,hl,hu,heq⟩:=
    CascadeAncestry.reachable_even_reset_parent q hr (by omega)
  have hk:k=n-2:=CascadeUniformFatal.even_band_scale_unique
    q k (n-2) ⟨hl,hu⟩ hband
  rw [hk] at heq
  have hP:2^n%3=n%3:=pow_matches_index n hsector
  have hgap:2^n<h∧2*h+2<3*2^n:=by omega
  have hmodh:h%3≠2:=by omega
  exact (CascadeSweep.root_excludes_nonimage h hmodh
    (CascadeForkOddDead.gap_avoids_even_images n h (by omega)
      hgap.1 hgap.2)) hreach

private theorem power_halve1 (n:Nat) (hn:2≤n):
    2^n=2*2^(n-1):=by
  have he:n=(n-1)+1:=by omega
  calc
    2^n=2^((n-1)+1):=congrArg (fun t:Nat=>2^t) he
    _=2*2^(n-1):=by rw[Nat.pow_succ];omega

/-- When the t=1 odd candidate lies on the other congruence side q%3=2,
    it is still excluded whenever 9 does not divide its own output numerator.
    This handles a second source-authentic family of actual odd forks. -/
theorem odd_tone_parent_unreachable_no9 (n j q d:Nat) (hn:6≤n)
    (hsector:n%6=4∨n%6=5)
    (hmargin:16*deficit n j+27*n+16≤2^n)
    (hd:9*d+2*deficit n j=8*2^n+5)
    (hq:q+2*2^n+n+3=4*d)
    (hmod:q%3=2) (hnot9:(2*q+5)%9≠0):
    ¬CascadeSweep.ReachC (2,0) (q,0):=by
  intro hr
  have hp2:=power_halve2 n (by omega:4≤n)
  have hp1:=power_halve1 n (by omega:2≤n)
  have hband:6*2^(n-2)-1≤q∧q≤8*2^(n-2)-3:=by omega
  have hnear:3*2^(n-1)≤q∧q≤4*2^(n-1):=by omega
  have hpositive:2*2^n+(n-2)≤2*q:=by omega
  let w:=2*q-(2*2^n+(n-2))
  have hsource:w+2*2^n+(n-2)=2*q:=by dsimp[w];omega
  have hgap:2^n<w∧2*w+2<3*2^n:=by omega
  have hP:2^n%3=n%3:=pow_matches_index n hsector
  have hmodw:w%3≠2:=by omega
  have hne:q≠2:=by omega
  have hc:ResetChain 2 q:=(root_reset_chain_iff q).mp hr
  obtain ⟨h,hchain,hparent⟩:=CascadeUniformFatal.reset_chain_last hc hne
  have hqeq:h=w:=CascadeAgent10Four.any_parent_near_top
     q (n-1) (n-2) w h (by omega) hnear.1 hnear.2
     hnot9 hband (by
       have hpow:8*2^(n-2)=2*2^n:=by omega
       rw[hpow]
       omega) hparent
  rw[hqeq] at hchain
  have hreach:CascadeSweep.ReachC (2,0) (w,0):=
    (root_reset_chain_iff w).mpr hchain
  exact (CascadeSweep.root_excludes_nonimage w hmodw
    (CascadeForkOddDead.gap_avoids_even_images n w (by omega)
      hgap.1 hgap.2)) hreach

/-- Exact valuation-two subcase with quotient Z/9 congruent to one modulo three.
    The source-rooted first-level odd candidate is uniformly excluded. -/
theorem odd_tone_quotient_one_dead (n j q d:Nat) (hn:6≤n)
    (hsector:n%6=4∨n%6=5)
    (hmargin:16*deficit n j+27*n+16≤2^n)
    (hd:9*d+2*deficit n j=8*2^n+5)
    (hq:q+2*2^n+n+3=4*d)
    (hmodd:d%3=1):
    ¬CascadeSweep.ReachC (2,0) (q,0):=by
  have hP:=pow_matches_index n hsector
  have hqmod:q%3=1:=by omega
  exact odd_tone_parent_unreachable n j q d (by omega) hsector
    hmargin hd hq hqmod

/-- Quotient Z/9 congruent to two modulo three is also pruned unless the
    resulting odd candidate itself has a nine-divisible output numerator. -/
theorem odd_tone_quotient_two_dead_no9 (n j q d:Nat) (hn:6≤n)
    (hsector:n%6=4∨n%6=5)
    (hmargin:16*deficit n j+27*n+16≤2^n)
    (hd:9*d+2*deficit n j=8*2^n+5)
    (hq:q+2*2^n+n+3=4*d)
    (hmodd:d%3=2) (hnot9:(2*q+5)%9≠0):
    ¬CascadeSweep.ReachC (2,0) (q,0):=by
  have hP:=pow_matches_index n hsector
  have hqmod:q%3=2:=by omega
  exact odd_tone_parent_unreachable_no9 n j q d hn hsector
    hmargin hd hq hqmod hnot9

#print axioms odd_tone_parent_unreachable
#print axioms odd_tone_parent_unreachable_no9
#print axioms odd_tone_quotient_one_dead
#print axioms odd_tone_quotient_two_dead_no9
end CascadeRayForkPrune

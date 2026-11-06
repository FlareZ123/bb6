import ForkOddDead27
import OddRayForced
set_option maxHeartbeats 0
namespace CascadeRayOddStrip
open CascadeResetInverse CascadeSweep CascadeUniformFatal CascadeAgent10Four
open CascadeForkOddDead CascadeForkOddDead27

/-- Generalized source first-parent classification for the narrow dyadic
fork-child band: low-valuation odd parents fall into two open image gaps. -/
theorem no27_parent_is_even_at_gap
  (n h w:Nat) (hn:5≤n)
  (hband:6*2^(n-2)-1≤h ∧ h≤8*2^(n-2)-3)
  (hnear:3*2^(n-1)≤h ∧ h≤4*2^(n-1))
  (hparent:2*h=8*2^(n-2)+w+(n-2))
  (hdiv:(2*h+5)%27≠0)
  (hoddgap:∀d, 2*h+5=9*d →
    2^(n-1)<2*d ∧ 2*(2*d)+2<3*2^(n-1))
  (q:Nat) (hq:ResetParent q h) : q=w := by
  rcases hq with ⟨k,hb,heq⟩ | ⟨k,t,d,hd,hb,hout,heq⟩
  · have hk:k=n-2:=even_band_scale_unique h k (n-2) hb hband
    rw [hk] at heq
    omega
  · by_cases ht0:t=0
    · subst t
      have hq:2*h+5=3*d:=by simpa using hout
      exact False.elim (near_top_no_odd_tzero h (n-1) (by omega)
        hnear.1 hnear.2 ⟨k,d,by simpa using hb,hq⟩)
    · by_cases ht1:t=1
      · subst t
        have hq:2*h+5=9*d:=by simpa using hout
        have hbounds:=hoddgap d hq
        exact False.elim ((gap_avoids_odd_images (n-1) (2*d)
          hbounds.1 hbounds.2) k (by simpa using hb))
      · have ht2:2≤t:=by omega
        have hex:t+1=3+(t-2):=by omega
        have hz:3^(t+1)%27=0:=by
          rw [hex,Nat.pow_add]
          simp
        have hzero:(2*h+5)%27=0:=by
          rw [hout,Nat.mul_mod,hz]
          simp
        exact False.elim (hdiv hzero)

/-- Rooted exclusion of any narrow-band target, independent of whether
it is an actual fatal ray height. -/
theorem no27_root_forbidden_at_gap
  (n h w:Nat) (hn:5≤n)
  (hband:6*2^(n-2)-1≤h ∧ h≤8*2^(n-2)-3)
  (hnear:3*2^(n-1)≤h ∧ h≤4*2^(n-1))
  (hparent:2*h=8*2^(n-2)+w+(n-2))
  (hdiv:(2*h+5)%27≠0)
  (hoddgap:∀d, 2*h+5=9*d →
    2^(n-1)<2*d ∧ 2*(2*d)+2<3*2^(n-1))
  (hwgap:2^n<w ∧ 2*w+2<3*2^n)
  (hwmod:w%3≠2) : ¬ReachC (2,0) (h,0) := by
  intro hr
  have hne:h≠2:=by
    have hp:1≤2^(n-2):=Nat.one_le_pow (n-2) 2 (by decide)
    omega
  have hc:ResetChain 2 h:=(root_reset_chain_iff h).mp hr
  obtain ⟨q,hchain,hq⟩:=reset_chain_last hc hne
  have hqw:q=w:=no27_parent_is_even_at_gap n h w hn
    hband hnear hparent hdiv hoddgap q hq
  subst q
  have hreach:ReachC (2,0) (w,0):=(root_reset_chain_iff w).mpr hchain
  exact (root_excludes_nonimage w hwmod
    (gap_avoids_even_images n w (by omega) hwgap.1 hwgap.2)) hreach

/-- The affine equation for a t=1 off-ray fork puts the even parent
    and both small odd valuations in strict dyadic image gaps, uniformly
    at arbitrary canonical ray depth. The scaled margin is explicit. -/
theorem ray_offfork_geometry (n D h w:Nat) (hn:13≤n)
  (hmargin:32*D+64*n+128≤2^n)
  (hlinear:9*h+8*D+9*n+7=14*2^n)
  (hparent:2*h=2*2^n+w+(n-2)) :
  (6*2^(n-2)-1≤h ∧ h≤8*2^(n-2)-3) ∧
  (3*2^(n-1)≤h ∧ h≤4*2^(n-1)) ∧
  (∀d, 2*h+5=9*d →
    2^(n-1)<2*d ∧ 2*(2*d)+2<3*2^(n-1)) ∧
  (2^n<w ∧ 2*w+2<3*2^n) := by
  have htwo:2^n=2*2^(n-1):=by
    have he:n=(n-1)+1:=by omega
    calc
      2^n=2^((n-1)+1):=congrArg (fun x:Nat=>2^x) he
      _=2*2^(n-1):=by rw[Nat.pow_succ];omega
  have hfour:2^n=4*2^(n-2):=by
    have he:n=(n-2)+2:=by omega
    calc
      2^n=2^((n-2)+2):=congrArg (fun x:Nat=>2^x) he
      _=4*2^(n-2):=by rw[Nat.pow_add];omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · intro d hd
    constructor <;> omega
  · constructor <;> omega

/-- Uniform genuine blank-root exclusion of every low-valuation off-ray
    t=1 fork whose canonical ray deficit occupies the high-margin strip.
    No assumption about the reachability of the parent ray is made. -/
theorem offray_fork_dead_no27 (n D h w:Nat) (hn:13≤n)
  (hmargin:32*D+64*n+128≤2^n)
  (hlinear:9*h+8*D+9*n+7=14*2^n)
  (hparent:2*h=2*2^n+w+(n-2))
  (hdiv:(2*h+5)%27≠0)
  (hwmod:w%3≠2) : ¬ReachC (2,0) (h,0) := by
  obtain ⟨hb, hnear, hodd, hgap⟩ :=
    ray_offfork_geometry n D h w hn hmargin hlinear hparent
  have hp:2^n=4*2^(n-2):=by
    have he:n=(n-2)+2:=by omega
    calc
      2^n=2^((n-2)+2):=congrArg (fun x:Nat=>2^x) he
      _=4*2^(n-2):=by rw[Nat.pow_add];omega
  have heq:2*h=8*2^(n-2)+w+(n-2):=by omega
  exact no27_root_forbidden_at_gap n h w (by omega) hb hnear heq
    hdiv hodd hgap hwmod

/-- The exact source odd t=1 first-reset branch at scale n-2 has the
    same linear equation for an arbitrary canonical even-ray depth. -/
theorem tone_linear (n j h d:Nat) (hn:13≤n)
  (hmargin:32*CascadeOddRay.deficit n j+64*n+128≤2^n)
  (hz:2*CascadeOddRay.ray n j+5=9*d)
  (heq:4*d=8*2^(n-2)+h+(n-2)+5) :
  9*h+8*CascadeOddRay.deficit n j+9*n+7=14*2^n := by
  have hs: CascadeOddRay.ray n j + CascadeOddRay.deficit n j =4*2^n:=by
    dsimp[CascadeOddRay.ray]
    omega
  have hp:2^n=4*2^(n-2):=by
    have hn':n=(n-2)+2:=by omega
    calc
      2^n=2^((n-2)+2):=congrArg (fun x:Nat=>2^x) hn'
      _=4*2^(n-2):=by rw[Nat.pow_add];omega
  omega

private theorem pow_period_six_mod3 (n:Nat):2^(n+6)%3=2^n%3:=by
  rw[Nat.pow_add]
  simp[Nat.mul_mod]

private theorem pow_mod_six_mod3 (n:Nat):2^n%3=2^(n%6)%3:=by
  induction n using Nat.strongRecOn with
  | ind n ih=>
    by_cases hn:n<6
    · simp[Nat.mod_eq_of_lt hn]
    · have hm:n-6<n:=by omega
      have he:n=(n-6)+6:=by omega
      rw[he,pow_period_six_mod3,ih (n-6) hm]
      have hh:((n-6)+6)%6=(n-6)%6:=by omega
      rw[hh]

private theorem parent_mod_restricted (n h w:Nat) (hn:13≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hparent:2*h=2*2^n+w+(n-2))
  (hmod:h%3≠0) : w%3≠2 := by
  have hp:=pow_mod_six_mod3 n
  rcases hsector with h4|h5
  · have hpow:2^n%3=1:=by rw[hp,h4]
    omega
  · have hpow:2^n%3=2:=by rw[hp,h5]
    omega

/-- The t=1 source-odd predecessor of any admissible high-margin ray
    level is genuinely inaccessible from the post-initial blank root,
    provided its low-valuation and residue constraints hold. The depth j
    is arbitrary. Its high-valuation exceptional branches remain open. -/
theorem source_tone_ray_fork_dead (n j h d:Nat) (hn:13≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hmargin:32*CascadeOddRay.deficit n j+64*n+128≤2^n)
  (hz:2*CascadeOddRay.ray n j+5=9*d)
  (heq:4*d=8*2^(n-2)+h+(n-2)+5)
  (hmod:h%3≠0) (hdiv:(2*h+5)%27≠0) :
  ¬ReachC (2,0) (h,0) := by
  let w:Nat:=2*h-(2*2^n+(n-2))
  have hl:=tone_linear n j h d hn hmargin hz heq
  have hpositive:2*2^n+(n-2)≤2*h:=by omega
  have hparent:2*h=2*2^n+w+(n-2):=by dsimp[w];omega
  have hwmod:=parent_mod_restricted n h w hn hsector hparent hmod
  exact offray_fork_dead_no27 n (CascadeOddRay.deficit n j) h w
    hn hmargin hl hparent hdiv hwmod

/-- A depth-12 odd fork with a genuine #746 high-index source shape.
    The number is an off-ray ancestor candidate, not a reached state. -/
example : ¬ReachC (2,0) (12870538,0) := by
  apply source_tone_ray_fork_dead 23 12 12870538 7411945
  all_goals decide

#print axioms source_tone_ray_fork_dead
#print axioms offray_fork_dead_no27
#print axioms no27_root_forbidden_at_gap
end CascadeRayOddStrip

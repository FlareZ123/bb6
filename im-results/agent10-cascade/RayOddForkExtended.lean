import RayOddForkStrip
set_option maxHeartbeats 0
namespace CascadeRayOddStrip
open CascadeResetInverse CascadeSweep CascadeUniformFatal CascadeAgent10Four
open CascadeForkOddDead CascadeForkOddDead27

/-- A reset in the narrow upper section of the dyadic middle gap cannot
    have a first-reset parent if its odd numerator has 3-adic order <=1.
    This applies even to targets with residue 2 modulo 3. -/
theorem narrow_gap_no_reset_parent (n w q:Nat) (hn:5≤n)
  (hl:2^n<w) (hu:8*w+32<9*2^n)
  (hdiv:(2*w+5)%9≠0) (hq:ResetParent q w) : False := by
  have hs:2^n=2*2^(n-1):=by
    have he:n=(n-1)+1:=by omega
    calc
      2^n=2^((n-1)+1):=congrArg (fun x:Nat=>2^x) he
      _=2*2^(n-1):=by rw[Nat.pow_succ];omega
  rcases hq with ⟨k,hb,heq⟩|⟨k,t,d,hd,hb,hout,heq⟩
  · have hg:2*w+2<3*2^n:=by omega
    exact (gap_avoids_even_images n w (by omega) hl hg k hb)
  · by_cases ht0:t=0
    · subst t
      have hz:2*w+5=3*d:=by simpa using hout
      have hlow:2^(n-1)<d:=by omega
      have hhigh:2*d+2<3*2^(n-1):=by omega
      exact (gap_avoids_odd_images (n-1) d hlow hhigh k
        (by simpa using hb))
    · have ht:1≤t:=by omega
      have hex:t+1=2+(t-1):=by omega
      have hzero:3^(t+1)%9=0:=by
        rw[hex,Nat.pow_add];simp
      have hbad:(2*w+5)%9=0:=by
        rw[hout,Nat.mul_mod,hzero];simp
      exact hdiv hbad

/-- True-blank-root exclusion of the entire narrow gap, including its
    residue-two subset when that subset has no high odd valuation. -/
theorem narrow_gap_root_excluded (n w:Nat) (hn:5≤n)
  (hl:2^n<w) (hu:8*w+32<9*2^n)
  (hres:w%3≠2 ∨ (2*w+5)%9≠0) :
  ¬ReachC (2,0) (w,0) := by
  rcases hres with hres|hres
  · have hg:2*w+2<3*2^n:=by omega
    exact root_excludes_nonimage w hres
      (gap_avoids_even_images n w (by omega) hl hg)
  · intro hr
    have hne:w≠2:=by omega
    have hc:ResetChain 2 w:=(root_reset_chain_iff w).mp hr
    obtain ⟨q,hchain,hparent⟩:=reset_chain_last hc hne
    exact narrow_gap_no_reset_parent n w q hn hl hu hres hparent

/-- An arbitrary-depth ray t=1 off-fork with low 3-adic order is absent
    whenever its middle-gap forced parent lies in one of the two excluded
    root-gate types. -/
theorem offray_fork_dead_extended (n D h w:Nat) (hn:13≤n)
  (hmargin:32*D+64*n+128≤2^n)
  (hlinear:9*h+8*D+9*n+7=14*2^n)
  (hparent:2*h=2*2^n+w+(n-2))
  (hdiv:(2*h+5)%27≠0)
  (hres:w%3≠2 ∨ (2*w+5)%9≠0):
  ¬ReachC (2,0) (h,0) := by
  obtain ⟨hb,hnear,hodd,hgap⟩:=
    ray_offfork_geometry n D h w hn hmargin hlinear hparent
  have hs:2^n=4*2^(n-2):=by
    have he:n=(n-2)+2:=by omega
    calc
      2^n=2^((n-2)+2):=congrArg (fun x:Nat=>2^x) he
      _=4*2^(n-2):=by rw[Nat.pow_add];omega
  have heq:2*h=8*2^(n-2)+w+(n-2):=by omega
  have hupper:8*w+32<9*2^n:=by omega
  intro hr
  have hne:h≠2:=by omega
  have hc:ResetChain 2 h:=(root_reset_chain_iff h).mp hr
  obtain ⟨q,hchain,hq⟩:=reset_chain_last hc hne
  have he:q=w:=no27_parent_is_even_at_gap n h w (by omega)
    hb hnear heq hdiv hodd q hq
  subst q
  have hwreach:ReachC (2,0) (w,0):=(root_reset_chain_iff w).mpr hchain
  exact (narrow_gap_root_excluded n w (by omega) hgap.1 hupper hres) hwreach

#print axioms offray_fork_dead_extended

/-- Rooted exclusion for arbitrary ray t=1 odd forks whose forced parent
    has 3-adic numerator valuation exactly one, including the cases with
    h mod 3 = 0 omitted by the earlier residue-two gap criterion. -/
theorem source_tone_ray_fork_dead_low_w (n j h d:Nat) (hn:13≤n)
  (hmargin:32*CascadeOddRay.deficit n j+64*n+128≤2^n)
  (hz:2*CascadeOddRay.ray n j+5=9*d)
  (heq:4*d=8*2^(n-2)+h+(n-2)+5)
  (hdiv:(2*h+5)%27≠0)
  (hwdiv:(2*(2*h-(2*2^n+(n-2)))+5)%9≠0):
  ¬ReachC (2,0) (h,0) := by
  let w:Nat:=2*h-(2*2^n+(n-2))
  have hl:=tone_linear n j h d hn hmargin hz heq
  have hpositive:2*2^n+(n-2)≤2*h:=by omega
  have hparent:2*h=2*2^n+w+(n-2):=by dsimp[w];omega
  have hwdiv':(2*w+5)%9≠0:=by exact hwdiv
  exact offray_fork_dead_extended n (CascadeOddRay.deficit n j) h w
    hn hmargin hl hparent hdiv (Or.inr hwdiv')

/-- Combines the two rooted residue exclusions at every admissible depth. -/
theorem source_tone_ray_fork_dead_either (n j h d:Nat) (hn:13≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hmargin:32*CascadeOddRay.deficit n j+64*n+128≤2^n)
  (hz:2*CascadeOddRay.ray n j+5=9*d)
  (heq:4*d=8*2^(n-2)+h+(n-2)+5)
  (hdiv:(2*h+5)%27≠0)
  (hgate:h%3≠0 ∨ (2*(2*h-(2*2^n+(n-2)))+5)%9≠0):
  ¬ReachC (2,0) (h,0) := by
  rcases hgate with hmod|hwdiv
  · exact source_tone_ray_fork_dead n j h d hn hsector hmargin hz heq hmod hdiv
  · exact source_tone_ray_fork_dead_low_w n j h d hn hmargin hz heq hdiv hwdiv

/-- A depth-16 off-ray fork in the hard h mod 3 = 0 sector is
    excluded by the next ancestor's nondivisibility by nine. -/
example : ¬ReachC (2,0) (53444229342,0) := by
  apply source_tone_ray_fork_dead_low_w 35 16 53444229342 30540926529
  all_goals decide

#print axioms source_tone_ray_fork_dead_low_w
#print axioms source_tone_ray_fork_dead_either
end CascadeRayOddStrip

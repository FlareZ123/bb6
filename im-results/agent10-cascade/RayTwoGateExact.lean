import RayGapTone
set_option maxHeartbeats 0
namespace CascadeRayTwoGate
open CascadeResetInverse CascadeSweep CascadeUniformFatal
open CascadeForkOddDead CascadeForkOddDead27 CascadeRayOddStrip CascadeRayGapTone

/-- In the high-margin off-ray t=1 strip, low 3-adic valuation of h
    makes its unique source first-reset ancestor w an *exact* root-gate
    equivalent, with the two directions certified by ResetChain. -/
theorem offray_fork_root_iff_even (n D h w:Nat) (hn:13≤n)
  (hm:32*D+64*n+128≤2^n)
  (hl:9*h+8*D+9*n+7=14*2^n)
  (he:2*h=2*2^n+w+(n-2))
  (hdiv:(2*h+5)%27≠0):
  ReachC (2,0) (h,0) ↔ ReachC (2,0) (w,0) := by
  obtain ⟨hb,hnear,hodd,hgap⟩:=ray_offfork_geometry n D h w hn hm hl he
  have hp:2^n=4*2^(n-2):=by
    have heq:n=(n-2)+2:=by omega
    calc
      2^n=2^((n-2)+2):=congrArg (fun x:Nat=>2^x) heq
      _=4*2^(n-2):=by rw[Nat.pow_add];omega
  have hpar:2*h=8*2^(n-2)+w+(n-2):=by omega
  constructor
  · intro hr
    have hne:h≠2:=by omega
    have hc:ResetChain 2 h:=(root_reset_chain_iff h).mp hr
    obtain ⟨q,hqc,hq⟩:=reset_chain_last hc hne
    have hqeq:q=w:=no27_parent_is_even_at_gap n h w (by omega)
      hb hnear hpar hdiv hodd q hq
    subst q
    exact (root_reset_chain_iff w).mpr hqc
  · intro hw
    have hc:ResetChain 2 w:=(root_reset_chain_iff w).mp hw
    have hparent:ResetParent w h:=Or.inl ⟨n-2,hb,hpar⟩
    exact (root_reset_chain_iff h).mpr (ResetChain.append hc hparent)

/-- An exact second-generation source-root gate for arbitrary off-ray
    t=1 forks: if h and its forced w each have 3-adic order <3, then
    h is rooted iff w's genuine odd t=1 parent is rooted, with every
    admissible (q,k,d) retained in the quantified witness. -/
theorem offray_fork_root_iff_second_tone (n D h w:Nat) (hn:13≤n)
  (hm:32*D+64*n+128≤2^n)
  (hl:9*h+8*D+9*n+7=14*2^n)
  (he:2*h=2*2^n+w+(n-2))
  (hdiv:(2*h+5)%27≠0)
  (wdiv:(2*w+5)%27≠0):
  ReachC (2,0) (h,0) ↔
    ∃(q k d:Nat), ReachC (2,0) (q,0) ∧
      d%2=1 ∧
      (6*2^k+1≤2*d ∧ 2*d≤8*2^k-1) ∧
      2*w+5=9*d ∧ 4*d=8*2^k+q+k+5 := by
  have hg:=ray_offfork_geometry n D h w hn hm hl he
  exact (offray_fork_root_iff_even n D h w hn hm hl he hdiv).trans
    (narrow_gap_root_iff_tone n w (by omega) hg.2.2.2.1 (by omega) wdiv)

#print axioms offray_fork_root_iff_even
#print axioms offray_fork_root_iff_second_tone
end CascadeRayTwoGate

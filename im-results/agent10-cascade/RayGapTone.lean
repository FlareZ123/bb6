import RayOddForkExtended
set_option maxHeartbeats 0
namespace CascadeRayGapTone
open CascadeResetInverse CascadeSweep CascadeUniformFatal
open CascadeForkOddDead CascadeForkOddDead27

/-- Every exact first reset parent of a narrow dyadic middle-gap height,
    when its numerator has 3-adic valuation <3, necessarily comes from
    precisely t=1 of the odd arm; the scale k and odd d are still honest
    source witnesses, not arbitrary surrogates. -/
theorem narrow_gap_parent_must_be_tone (n w q:Nat) (hn:5≤n)
  (hl:2^n<w) (hu:8*w+32<9*2^n)
  (hdiv:(2*w+5)%27≠0) (hq:ResetParent q w) :
  ∃k d, d%2=1 ∧
    (6*2^k+1≤2*d ∧ 2*d≤8*2^k-1) ∧
    2*w+5=9*d ∧ 4*d=8*2^k+q+k+5 := by
  have hs:2^n=2*2^(n-1):=by
    have he:n=(n-1)+1:=by omega
    calc
      2^n=2^((n-1)+1):=congrArg (fun x:Nat=>2^x) he
      _=2*2^(n-1):=by rw[Nat.pow_succ];omega
  rcases hq with ⟨k,hb,heq⟩|⟨k,t,d,hd,hb,hout,heq⟩
  · have hg:2*w+2<3*2^n:=by omega
    exact False.elim (gap_avoids_even_images n w (by omega) hl hg k hb)
  · by_cases ht0:t=0
    · subst t
      have hz:2*w+5=3*d:=by simpa using hout
      have hlow:2^(n-1)<d:=by omega
      have hhigh:2*d+2<3*2^(n-1):=by omega
      exact False.elim (gap_avoids_odd_images (n-1) d hlow hhigh k
        (by simpa using hb))
    · by_cases ht1:t=1
      · subst t
        refine ⟨k,d,hd,?_,?_,?_⟩
        · simpa using hb
        · simpa using hout
        · omega
      · have ht2:2≤t:=by omega
        have hex:t+1=3+(t-2):=by omega
        have hzero:3^(t+1)%27=0:=by
          rw[hex,Nat.pow_add];simp
        have hbad:(2*w+5)%27=0:=by
          rw[hout,Nat.mul_mod,hzero];simp
        exact False.elim (hdiv hbad)

/-- A complete exact *iff* true-root criterion for the narrow upper dyadic
    gap under the secondary no-27 gate. Every true root path to w must
    pass through a genuine t=1 odd parent, and every such parent's rooted
    path gives a rooted path to w. This result retains all possible k. -/
theorem narrow_gap_root_iff_tone (n w:Nat) (hn:5≤n)
  (hl:2^n<w) (hu:8*w+32<9*2^n)
  (hdiv:(2*w+5)%27≠0):
  ReachC (2,0) (w,0) ↔
    ∃(q k d:Nat), ReachC (2,0) (q,0) ∧
      d%2=1 ∧
      (6*2^k+1≤2*d ∧ 2*d≤8*2^k-1) ∧
      2*w+5=9*d ∧ 4*d=8*2^k+q+k+5 := by
  constructor
  · intro hr
    have hne:w≠2:=by omega
    have hc:ResetChain 2 w:=(root_reset_chain_iff w).mp hr
    obtain ⟨q,hqc,hparent⟩:=reset_chain_last hc hne
    obtain ⟨k,d,hd,hband,hz,heq⟩:=narrow_gap_parent_must_be_tone n w q hn hl hu hdiv hparent
    exact ⟨q,k,d,(root_reset_chain_iff q).mpr hqc,hd,hband,hz,heq⟩
  · rintro ⟨q,k,d,hroot,hd,hband,hz,heq⟩
    have hparent:ResetParent q w:=Or.inr ⟨k,1,d,hd,by simpa using hband,
      by simpa using hz,by omega⟩
    have hqc:ResetChain 2 q:=(root_reset_chain_iff q).mp hroot
    exact (root_reset_chain_iff w).mpr (ResetChain.append hqc hparent)

#print axioms narrow_gap_root_iff_tone
end CascadeRayGapTone

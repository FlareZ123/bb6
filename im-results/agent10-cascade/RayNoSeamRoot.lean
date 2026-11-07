import EvenChainFork
import RayNoSeamWalk
import RayNoSeamResidue
set_option maxHeartbeats 0
namespace CascadeSeam
open CascadeOddRay CascadeEvenChainGap CascadeEvenChainFork

private theorem deficit_closed (n j:Nat) (hn:1≤n):
  deficit n j+(n-1)=2^j*(2*n+3) := by
  induction j with
  | zero =>
    simp [deficit]
    omega
  | succ j ih =>
    have hp:2^(j+1)=2*2^j:=by rw[Nat.pow_succ];omega
    have hr:deficit n (j+1)=2*deficit n j+(n-1):=rfl
    rw[hr,hp]
    have hmul:(2*2^j)*(2*n+3)=2*(2^j*(2*n+3)):=by ac_rfl
    rw[hmul]
    omega

/-- Every genuine #746 weak-margin low-valuation second-tier t=1
    reset ancestor is blank-root inaccessible, uniformly for all
    n≥20 and any ray depth j, without finite enumeration. The hypotheses
    are the exact source inverse equations, a physical odd-image band,
    both exact valuation-one conditions, and the true blank-root relation. -/
theorem weak_margin_source_t1_gap_dead (n j h w q d:Nat)
 (hn:20≤n)
 (hsector:n%6=4 ∨ n%6=5)
 (hm:32*deficit n j+64*n+128≤2^n)
 (hl:9*h+8*deficit n j+9*n+7=14*2^n)
 (he:2*h=2*2^n+w+(n-2))
 (hdiv:(2*h+5)%27≠0)
 (wdiv:(2*w+5)%27≠0)
 (hw:2*w+5=9*d)
 (hband:6*2^(n-4)+1≤2*d ∧ 2*d≤8*2^(n-4)-1)
 (hq:4*d=8*2^(n-4)+q+(n-4)+5):
 ¬CascadeSweep.ReachC (2,0) (h,0) := by
  have hdef:=deficit_closed n j (by omega)
  obtain ⟨hb,hs,hmargin⟩:=
    second_fork_to_seam n j (deficit n j) h w q d hn hdef hm hl he hw hq
  obtain ⟨r,hr,hi,hg⟩:=weak_margin_inverse_exit n j q hn hs hmargin hb
  have hdnot:d%3≠0:=valuation_not_three w d hw wdiv
  have hres:=source_second_safe n q d hn hsector hdnot hq
  have hsafe:SafeResidue (n-4) q:=⟨hres.1,Or.inl hres.2⟩
  exact weak_margin_two_tier_gap_dead n (deficit n j) h w q d r (by omega)
    hm hl he hdiv wdiv hw hband hq hsafe hi hg.1 hg.2

#print axioms weak_margin_source_t1_gap_dead
end CascadeSeam

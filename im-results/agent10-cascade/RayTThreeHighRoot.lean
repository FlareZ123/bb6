import RayTThreeHighGeometry
import RayTThreeTwoGate
set_option maxHeartbeats 0
namespace CascadeTThreeLow
open CascadeResetInverse CascadeSweep CascadeUniformFatal CascadeForkOddDead

/-- Source-root exclusion of the immediate t=3 high-valuation ancestor:
    when its reset height r is 0 mod3, its only first predecessor is a
    forced even step into a strict no-even-image gap, whose residue is
    also 0 mod3. This uses the complete, original-source ResetParent
    grammar and the actual blank-reset ReachC, with no finite cutoff. -/
theorem third_high_child_zero_root_dead (n q d r r1:Nat) (hn:20≤n)
 (hsector:n%6=4 ∨ n%6=5)
 (hlo:9*2^(n-4)+5*n+40≤q)
 (htight:8*q+40*n+320≤75*2^(n-4))
 (hz:2*q+5=81*d)
 (he:16*d=8*2^(n-6)+r+(n-6)+5)
 (hev:2*r=8*2^(n-6)+r1+(n-6))
 (hrmod:r%3=0):
 ¬ReachC (2,0) (r,0) := by
  have hgeometry:=third_high_child_one_even_gap n q d r r1 hn hlo htight hz he hev
  have hrgap:=third_high_child_gap_strong n q d r r1 hn hlo htight hz he hev
  have hr1mod:=high_child_even_mod_zero n r r1 hn hsector hrmod hev
  have hne:r≠2:=by
    have hp:0<2^(n-6):=Nat.pow_pos (by decide)
    omega
  intro hroot
  have hchain:ResetChain 2 r:=(root_reset_chain_iff r).mp hroot
  obtain ⟨a,ha,hparent⟩:=reset_chain_last hchain hne
  have hunique:a=r1:=any_parent_equals_even r (n-6) r1 a hgeometry.1
    hev (by omega) hparent
  subst a
  have hreach:ReachC (2,0) (r1,0):=(root_reset_chain_iff r1).mpr ha
  exact (root_excludes_nonimage r1 (by omega)
    (gap_avoids_even_images (n-4) r1 (by omega) hrgap.1 hrgap.2)) hreach

#print axioms third_high_child_zero_root_dead
end CascadeTThreeLow

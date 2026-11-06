import EvenChainGap
import RayTwoGateExact
set_option maxHeartbeats 0
namespace CascadeEvenChainFork
open CascadeResetInverse CascadeSweep CascadeEvenChainGap CascadeRayTwoGate

/-- Distinct failed-sweep dyadic odd-image bands never overlap. -/
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

/-- A genuinely rooted weak-margin t=1 off-ray fork whose next
    exceptional t=1 ancestor exits the dyadic image gap is impossible.
    The chain length r is unbounded and the exact second-level odd
    inverse is retained without discarding other source possibilities. -/
theorem weak_margin_two_tier_gap_dead
  (n D h w q d r:Nat)
  (hn:13≤n)
  (hm:32*D+64*n+128≤2^n)
  (hl:9*h+8*D+9*n+7=14*2^n)
  (he:2*h=2*2^n+w+(n-2))
  (hdiv:(2*h+5)%27≠0)
  (wdiv:(2*w+5)%27≠0)
  (hw:2*w+5=9*d)
  (hband:6*2^(n-4)+1≤2*d ∧ 2*d≤8*2^(n-4)-1)
  (hq:4*d=8*2^(n-4)+q+(n-4)+5)
  (hs:SafeResidue (n-4) q)
  (hb:∀i<r,6*2^(n-4)-1≤evenWalk (n-4) q i ∧
      evenWalk (n-4) q i≤8*2^(n-4)-3)
  (hgaplo:4*2^(n-4)-3<evenWalk (n-4) q r)
  (hgaphi:evenWalk (n-4) q r<6*2^(n-4)-1):
  ¬ReachC (2,0) (h,0):=by
  have hqnot:¬ReachC (2,0) (q,0):=
    walk_exits_gap_unreachable (n-4) q r (by omega) hs hb
      hgaplo hgaphi
  intro hroot
  obtain ⟨q',k',d',hqr,hdodd,hband',hw',he'⟩:=
    (offray_fork_root_iff_second_tone n D h w hn hm hl he
      hdiv wdiv).mp hroot
  have hdd:d'=d:=by omega
  subst d'
  have hkk:k'=n-4:=odd_band_unique (2*d) k' (n-4)
    hband' hband
  rw[hkk] at he'
  have hqq:q'=q:=by omega
  rw[hqq] at hqr
  exact hqnot hqr

/-- An explicit original-source high-margin countercheck:
    the weaker 32D margin holds at n=28, depth 16, whereas Agent 10's
    earlier 2048D high-margin theorem does not apply. The secondary
    t=1 parent has a two-step even chain ending in a forbidden gap. -/
theorem offray_28_16_unreachable:
  ¬ReachC (2,0) (414129261,0):=by
  apply weak_margin_two_tier_gap_dead 28 3866597
    414129261 291387584 124793431 64752797 2
  all_goals try decide
  · intro i hi
    have h:i=0∨i=1:=by omega
    rcases h with rfl|rfl <;> decide

#print axioms weak_margin_two_tier_gap_dead
#print axioms offray_28_16_unreachable
end CascadeEvenChainFork

import EvenOddAllDepthShortExtensions
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13AllDepthSieve67

/-- A uniformly source-certified parent exclusion sieve for every
    possible odd bounce depth. Additional AOB, AOE and OBBB paths
    increase the formal phase/q residue coverage from 63 to 67 of
    128 cells for each r. These are NOT counts of actual machine halts. -/
def sourceOddDepthPruned67 (n q : Nat) : Prop :=
  BB6.Agent13AllDepthSieve.sourceOddDepthPruned n q ∨
  (n%8=4 ∧ (q+9*(n/8))%32=14) ∨
  (n%8=6 ∧ ((q+15*(n/8))%16=2 ∨
            (q+31*(n/8))%32=20))

/-- Exact original section reachability exclusion, arbitrary depth.
    Every newly admitted short-word phase reaches the genuine
    blank-forbidden odd-right image via source-certified inverse laws. -/
theorem source_odd_depth_pruned67_unreachable
    (u a k n q : Nat) (hq : 1≤q) (hk : 80≤k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*n=512*u+78)
    (hpruned : sourceOddDepthPruned67 n q) :
    ¬ BB6.Agent3.CReach a k := by
  rcases hpruned with hpOld | ⟨hp4, hp4r⟩ | ⟨hp6,hphase⟩
  · exact BB6.Agent13AllDepthSieve.source_odd_depth_pruned_unreachable
      u a k n q hq hk ha hcost hpOld
  · let r := n/8
    have hn : n=8*r+4 := by
      have h := Nat.mod_add_div n 8
      dsimp [r]
      omega
    rw [hn] at hcost
    have hres : (q+9*r)%32=14 := by dsimp [r] at *; exact hp4r
    exact BB6.Agent13AllDepthShort.depth_four_OBBB_parent_impossible
      u a k r q hq hk ha (by omega) hres
  · let r := n/8
    have hn : n=8*r+6 := by
      have h := Nat.mod_add_div n 8
      dsimp [r]
      omega
    rw [hn] at hcost
    rcases hphase with hpAOB | hpAOE
    · have hp : (q+15*r)%16=2 := by dsimp [r] at *; exact hpAOB
      exact BB6.Agent13AllDepthShort.depth_six_AOB_parent_impossible
        u a k r q hq hk ha (by omega) hp
    · have hp : (q+31*r)%32=20 := by dsimp [r] at *; exact hpAOE
      exact BB6.Agent13AllDepthShort.depth_six_AOE_parent_impossible
        u a k r q hq hk ha (by omega) hp

/-- Source arithmetic supplies the uniform quotient via an exact
    high-power equation, not an inferred quotient from finite samples. -/
theorem source_odd_depth_pruned67_high_valuation
    (u a k n q : Nat) (hq : 1≤q) (hk : 80≤k)
    (hmass : 346*u+54=2^(n+4)*q)
    (hparent : 346*u+54=2^(n+1)*(a+3))
    (hcost : 2*k+a+7+3*n=512*u+78)
    (hpruned : sourceOddDepthPruned67 n q) :
    ¬ BB6.Agent3.CReach a k := by
  have hfactor : (2:Nat)^(n+4)=2^(n+1)*8 := by
    rw [show n+4=(n+1)+3 by omega,Nat.pow_add]
  have hmass' : 346*u+54=(2:Nat)^(n+1)*(8*q) := by
    rw [hfactor] at hmass
    calc
      346*u+54=(2:Nat)^(n+1)*8*q := hmass
      _=(2:Nat)^(n+1)*(8*q) := by ac_rfl
  have he : (2:Nat)^(n+1)*(a+3)=
      (2:Nat)^(n+1)*(8*q) := hparent.symm.trans hmass'
  have ha : a+3=8*q :=
    Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) he
  exact source_odd_depth_pruned67_unreachable
    u a k n q hq hk ha hcost hpruned

#print axioms source_odd_depth_pruned67_unreachable
#print axioms source_odd_depth_pruned67_high_valuation
end BB6.Agent13AllDepthSieve67

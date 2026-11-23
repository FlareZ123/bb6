import EvenOddAllDepthPhaseFour
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13AllDepthSieve

/-- Four source-inverse bounce phases, with the quotient congruences
    permitting a finite sequence of genuine original-section
    predecessor equivalences into the forbidden odd-right blank image.
    The parameter n is arbitrary: no recursion-depth cutoff is used. -/
def sourceOddDepthPruned (n q : Nat) : Prop :=
  n%8=0 ∨
  (n%8=2 ∧ (q+3*(n/8))%8=7) ∨
  (n%8=4 ∧ ((q+n/8)%8=4 ∨ (q+n/8)%16=3)) ∨
  (n%8=6 ∧ (q+n/8)%2=1)

/-- A source-only uniform theorem for the original Machine C left-odd
    bounce inverse fan at arbitrary depth n. Given the original exact
    source cost and parent quotient equations, every marked phase
    is inaccessible from the genuine blank section orbit. -/
theorem source_odd_depth_pruned_unreachable
    (u a k n q : Nat) (hq : 1≤q) (hk : 80≤k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*n=512*u+78)
    (hpruned : sourceOddDepthPruned n q) :
    ¬ BB6.Agent3.CReach a k := by
  dsimp [sourceOddDepthPruned] at hpruned
  rcases hpruned with h0|⟨h2,hqphase⟩|⟨h4,hqphase⟩|⟨h6,hqphase⟩
  · let r := n/8
    have hn : n=8*r := by
      have hh := Nat.mod_add_div n 8
      dsimp [r]
      omega
    rw [hn] at hcost
    exact BB6.Agent13AllDepth.depth_eight_odd_source_explicit_impossible
      u a k r q hq (by omega) ha (by omega)
  · let r := n/8
    have hn : n=8*r+2 := by
      have hh := Nat.mod_add_div n 8
      dsimp [r]
      omega
    have hp : (q+3*r)%8=7 := by dsimp [r] at *; exact hqphase
    rw [hn] at hcost
    exact BB6.Agent13AllDepth.depth_two_BBA_source_parent_impossible
      u a k r q hk ha (by omega) hp
  · let r := n/8
    have hn : n=8*r+4 := by
      have hh := Nat.mod_add_div n 8
      dsimp [r]
      omega
    rw [hn] at hcost
    rcases hqphase with hB|hF
    · have hp : (q+r)%8=4 := by dsimp [r] at *; exact hB
      exact BB6.Agent13AllDepthFour.depth_four_OB_parent_impossible
        u a k r q hq hk ha (by omega) hp
    · have hp : (q+r)%16=3 := by dsimp [r] at *; exact hF
      exact BB6.Agent13AllDepthFour.depth_four_OF_parent_impossible
        u a k r q hq hk ha (by omega) hp
  · let r := n/8
    have hn : n=8*r+6 := by
      have hh := Nat.mod_add_div n 8
      dsimp [r]
      omega
    have hp : (q+r)%2=1 := by dsimp [r] at *; exact hqphase
    rw [hn] at hcost
    exact BB6.Agent13AllDepth.depth_six_parity_source_parent_impossible
      u a k r q (by omega) ha (by omega) hp


/-- The exact original-section odd-left bounce power equation supplies
    a+3=8*q whenever the mass has three extra factors of two beyond
    the specific source bounce power. Thus the four-phase sieve works
    at *arbitrary* source bounce depth, without materializing the
    candidate parent quotient by subtraction or division. -/
theorem source_high_valuation_odd_depth_pruned_unreachable
    (u a k n q : Nat) (hq : 1≤q) (hk : 80≤k)
    (hmass : 346*u+54=2^(n+4)*q)
    (hparent : 346*u+54=2^(n+1)*(a+3))
    (hcost : 2*k+a+7+3*n=512*u+78)
    (hpruned : sourceOddDepthPruned n q) :
    ¬ BB6.Agent3.CReach a k := by
  have hfactor : (2:Nat)^(n+4)=2^(n+1)*8 := by
    rw [show n+4=(n+1)+3 by omega,Nat.pow_add]
  have hmass' : 346*u+54=(2:Nat)^(n+1)*(8*q) := by
    rw [hfactor] at hmass
    calc
      346*u+54=(2:Nat)^(n+1)*8*q := hmass
      _=(2:Nat)^(n+1)*(8*q) := by ac_rfl
  have he : (2:Nat)^(n+1)*(a+3)=
      (2:Nat)^(n+1)*(8*q) :=
    hparent.symm.trans hmass'
  have ha : a+3=8*q := Nat.eq_of_mul_eq_mul_left
    (Nat.pow_pos (by decide)) he
  exact source_odd_depth_pruned_unreachable
    u a k n q hq hk ha hcost hpruned

#print axioms source_odd_depth_pruned_unreachable
#print axioms source_high_valuation_odd_depth_pruned_unreachable
end BB6.Agent13AllDepthSieve

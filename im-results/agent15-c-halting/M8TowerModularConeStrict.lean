import M8OddTowerPrior
import ModularConeBlindHigh
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent15Research
open BB6.Agent42ModularCone

theorem towerIndex_positive_for_cone (m r t : Nat) (hm : m%2=1) :
    1≤towerIndex m r t := by
  have hR : 1≤towerR m r := by
    dsimp [towerR]
    omega
  have hm1 : 1≤m := by omega
  have hM : 2≤m+1 := by omega
  have hprod : 2≤towerR m r*(m+1) := by
    have h := Nat.mul_le_mul hR hM
    simpa using h
  dsimp [towerIndex]
  omega

/-- Every member of the all-odd M8 tower lies in the generic direct-chain
    blind cylinder of Agent42's adaptive modular high-stop filter. -/
theorem tower_modular_cone_blind (m r t : Nat)
    (hm : m%2=1) (hr : 1≤r) :
    highStopExcluded (towerIndex m r t+1) m = false := by
  have hj4 := towerIndex_mod_four m r t hr
  have hj2 : towerIndex m r t%2=0 := by omega
  have hdiv : 2^(2*m+2) ∣ towerIndex m r t+3*m+3 := by
    simpa [allOddB] using tower_prior_divisible m r t hr
  exact high_stop_blind_of_even_divisible (towerIndex m r t) m
    (towerIndex_positive_for_cone m r t hm) hj2 hm hdiv

/-- The all-odd M8 source obstruction is genuinely independent of the
    adaptive modular-cone component: the checker returns false while the
    source theorem proves the same exact target unreachable. -/
theorem tower_strict_beyond_modular_cone (m r t : Nat)
    (hm : m%2=1) (hr : 1≤r) :
    highStopExcluded (towerIndex m r t+1) m = false ∧
    ¬ BB6.Agent15.CReach
      (2*towerIndex m r t+3) (towerK m r t) :=
  ⟨tower_modular_cone_blind m r t hm hr,
   tower_every_odd_unreachable m r t hm hr⟩

#print axioms tower_modular_cone_blind
#print axioms tower_strict_beyond_modular_cone
end BB6.Agent15Research

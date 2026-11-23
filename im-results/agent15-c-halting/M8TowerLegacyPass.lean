import M8OddTowerPrior
import JointAllRoot
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research

/-- The full unbounded M8-excluded tower survives every restriction in
    the earlier Agent19Joint.highAllowed theorem, including Agent3 base
    and rectangular exclusions and all four special two-adic families. -/
theorem tower_passes_all_legacy_high_sieves (m r t : Nat)
    (hm : m%2=1) (hr : 1≤r) :
    BB6.Agent19Joint.highAllowed (towerIndex m r t) m := by
  let j := towerIndex m r t
  have hj4 : j%4=(m+1)%4 := towerIndex_mod_four m r t hr
  have hj2 : j%2=0 := by omega
  have hs : (j+m)%4=3 := by omega
  have hbase : BB6.Agent3.jointHighAllowed j m := by
    dsimp [BB6.Agent3.jointHighAllowed]
    omega
  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    dsimp [BB6.Agent3.jointHighRectAllowed]
    refine ⟨hbase,?_⟩
    omega
  change BB6.Agent3.jointHighRectAllowed j m ∧
    (∀ n, ¬(n+4≤2*m+2 ∧
       (j+3*m+3)%2^(n+4)=2^(n+2) ∧
       (2*j+3)%8=(if n%2=0 then 7 else 3))) ∧
    ¬ (2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) ∧
    ¬ (2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) ∧
    ¬ (3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) ∧
    ¬ (3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0)
  refine ⟨hrect, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rintro ⟨hn,hres,_⟩
    exact tower_prior_avoided m r t n hr hn hres
  all_goals omega

#print axioms tower_passes_all_legacy_high_sieves
end BB6.Agent15Research


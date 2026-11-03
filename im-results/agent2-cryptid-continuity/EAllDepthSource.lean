import Lean.Elab.Tactic.Omega
import DComplexity
import ERegularLadderSource

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.EAllDepthSource
open CryptidBoundary BB6.BoundaryPadding
open BB6.Agent31SecondSource BB6.EThirdSource
open BB6.ETripleLadderIndex BB6.ETripleLadderSource
open BB6.DComplexity BB6.ERegularLadderSource

/-- Definitional alignment of the independent coefficient-only model and the
    exact original-machine E source cost. -/
theorem kIndex_eq (m u : Nat) :
    BB6.DCostLower.kIndex m u = BB6.ETripleLadderSource.kIndex m u := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change 3*BB6.DCostLower.kIndex m u+2 =
      3*BB6.ETripleLadderSource.kIndex m u+2
    rw [ih]

theorem totalCost_eq (m u q : Nat) :
    BB6.DCostLower.totalCost m u q =
      BB6.ETripleLadderSource.totalCost m u q := by
  induction m generalizing u q with
  | zero => rfl
  | succ m ih =>
    change BB6.DCostLower.cost (BB6.DCostLower.kIndex (m+1) u) q +
      BB6.DCostLower.totalCost m (8*u+7) (q+2) =
      BB6.ETripleLadderSource.cost
        (BB6.ETripleLadderSource.kIndex (m+1) u) q +
      BB6.ETripleLadderSource.totalCost m (8*u+7) (q+2)
    rw [kIndex_eq (m+1) u, ih]
    rfl

/-- An ORIGINAL six-state primitive-run theorem for every positive prepared
    E-exception depth, with a regular-language input whose entire finite
    support is at most 120*3^m bits. The three preliminary checkpoints and
    m further E-ladder source steps are mathematically composed modulo the
    physically irrelevant terminal blank representation. The long E stage
    alone lasts at least 64^m original primitive transitions.

    This statement is about chosen synthetic start configurations. No blank
    tape reachability or BB(6) bound follows from it. -/
theorem all_positive_depth_original_source (m : Nat) (hm : 0 < m) :
    ∃ k q U p, 0 < U ∧ U < 512 ∧
      3*k+4+2*q+1 ≤ 120*3^m ∧
      64^m ≤ BB6.ETripleLadderSource.totalCost m (U-1) p ∧
      ((∃ r v, m=2*r ∧ k=9*v+7 ∧ q=3*r+3 ∧ p=1 ∧
          ObsEq
            (run ((firstCost (3*v+2) (3*r) + secondCost (3*v+2) +
                thirdBCost v) +
               BB6.ETripleLadderSource.totalCost m (U-1) p)
              (start (3*v+2) (3*r)))
            (physicalSection (3*8^m*U+1) (p+2*m) 0
               (List.replicate 6 true))) ∨
       (∃ r v, m=2*r+1 ∧ k=9*v+4 ∧ q=3*r+6 ∧ p=4 ∧
          ObsEq
            (run ((firstCost (3*v+1) (3*r+3) + secondCost (3*v+1) +
                thirdCost v) +
               BB6.ETripleLadderSource.totalCost m (U-1) p)
              (start (3*v+1) (3*r+3)))
            (physicalSection (3*8^m*U+1) (p+2*m) 0
               (List.replicate 6 true)))) := by
  obtain ⟨k,q,U,p,hpos,hlt,hsize,htime,hcases⟩ :=
    BB6.DComplexity.all_depth_synthetic m hm
  have hun : U-1+1=U := by omega
  have htimeSource :
      64^m ≤ BB6.ETripleLadderSource.totalCost m (U-1) p := by
    rw [← totalCost_eq]
    exact htime
  refine ⟨k,q,U,p,hpos,hlt,hsize,htimeSource,?_⟩
  rcases hcases with hEven | hOdd
  · obtain ⟨r,v,hme,hke,hqe,hpe,hnum⟩ := hEven
    refine Or.inl ⟨r,v,hme,hke,hqe,hpe,?_⟩
    have hn : 512*v+434=3^(m+1)*((U-1)+1)+1 := by
      rw [hun]
      exact hnum
    have hp : 2*(3*r)+3=3*m+3 := by omega
    have hs := original_B_then_ladder v (3*r) m (U-1) hn hp
    simpa only [hpe,hun] using hs
  · obtain ⟨r,v,hmo,hko,hqo,hpo,hnum⟩ := hOdd
    refine Or.inr ⟨r,v,hmo,hko,hqo,hpo,?_⟩
    have hn : 512*v+257=3^(m+1)*((U-1)+1)+1 := by
      rw [hun]
      exact hnum
    have hp : 2*(3*r+3)=3*m+3 := by omega
    have hs := original_E_then_ladder v (3*r+3) m (U-1) hn hp
    simpa only [hpo,hun] using hs

#print axioms kIndex_eq
#print axioms totalCost_eq
#print axioms all_positive_depth_original_source
end BB6.EAllDepthSource

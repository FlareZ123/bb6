import Lean.Elab.Tactic.Omega
import DComplexity
import EAllDepthSource
import ERegularLadderSafe

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace BB6.EAllDepthSafe
open CryptidBoundary BB6.Agent31SecondSource
open BB6.EThirdSource BB6.ERegularLadderSafe

/-- A source-kernel theorem of unbounded supercubic *prepared-input*
    primitive runtime: for EVERY m≥1, one of two explicitly given regular
    D-start F/0 inputs uses at most 120*3^m finite right-tape cells yet
    never enters the six-state machine's halt state through time 64^m.
    The multiplier U is explicitly constructible and bounded below 512.
    Nothing here asserts that a prepared input is reached from blank tape. -/
theorem regular_prepared_no_halt_through_64pow
    (m : Nat) (hm : 0 < m) :
    ∃ k q U p, 0<U ∧ U<512 ∧
      3*k+4+2*q+1 ≤ 120*3^m ∧
      ((∃ r v, m=2*r ∧ k=9*v+7 ∧ q=3*r+3 ∧ p=1 ∧
          ∀ t, t≤64^m →
            (run t (start (3*v+2) (3*r))).st ≠ 6) ∨
       (∃ r v, m=2*r+1 ∧ k=9*v+4 ∧ q=3*r+6 ∧ p=4 ∧
          ∀ t, t≤64^m →
            (run t (start (3*v+1) (3*r+3))).st ≠ 6)) := by
  obtain ⟨k,q,U,p,hpos,hlt,hsize,htime,hcases⟩ :=
    BB6.DComplexity.all_depth_synthetic m hm
  have hun : U-1+1=U := by omega
  have htimeSource :
      64^m ≤ BB6.ETripleLadderSource.totalCost m (U-1) p := by
    rw [← BB6.EAllDepthSource.totalCost_eq]
    exact htime
  refine ⟨k,q,U,p,hpos,hlt,hsize,?_⟩
  rcases hcases with he | ho
  · obtain ⟨r,v,hme,hke,hqe,hpe,hnum⟩ := he
    refine Or.inl ⟨r,v,hme,hke,hqe,hpe,?_⟩
    intro t ht
    have hn : 512*v+434=3^(m+1)*((U-1)+1)+1 := by
      rw [hun]
      exact hnum
    have hp : 2*(3*r)+3=3*m+3 := by omega
    have hbound :
        t ≤ (firstCost (3*v+2) (3*r) +
          secondCost (3*v+2) + thirdBCost v) +
          BB6.ETripleLadderSource.totalCost m (U-1) 1 := by
      rw [hpe] at htimeSource
      omega
    exact even_chain_no_halt v (3*r) m (U-1) hn hp t hbound
  · obtain ⟨r,v,hmo,hko,hqo,hpo,hnum⟩ := ho
    refine Or.inr ⟨r,v,hmo,hko,hqo,hpo,?_⟩
    intro t ht
    have hn : 512*v+257=3^(m+1)*((U-1)+1)+1 := by
      rw [hun]
      exact hnum
    have hp : 2*(3*r+3)=3*m+3 := by omega
    have hbound :
        t ≤ (firstCost (3*v+1) (3*r+3) +
          secondCost (3*v+1) + thirdCost v) +
          BB6.ETripleLadderSource.totalCost m (U-1) 4 := by
      rw [hpo] at htimeSource
      omega
    exact odd_chain_no_halt v (3*r+3) m (U-1) hn hp t hbound

#print axioms regular_prepared_no_halt_through_64pow
end BB6.EAllDepthSafe

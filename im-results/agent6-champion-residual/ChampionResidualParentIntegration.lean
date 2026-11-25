import ChampionResidualFrontier
import ChampionParentExact
import Canonical78ExactComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31ChampionParentIntegration

open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier
open BB6.Agent6ChampionResidual
open BB6.Agent13MixedBound109

/-- The Agent48 two-hole A/1–B/1 parent is the same partial table reached
    after Agent6's seven champion-path refinements. This is checked slot by
    slot, not inferred from the matching labels. -/
theorem parent_eq_championP7 :
    BB6.Agent48Parent.parent = BB6.Agent6ChampionResidual.championP7 := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;>
    decide [BB6.Agent48Parent.parent, BB6.Agent48Parent.parentM,
      BB6.Agent48Parent.a1, BB6.Agent47WeightedHalt.forgetHaltRows,
      BB6.Agent6ChampionResidual.championP7,
      BB6.Agent6ChampionResidual.championP6,
      BB6.Agent6ChampionResidual.championP5,
      BB6.Agent6ChampionResidual.championP4,
      BB6.Agent6ChampionResidual.championP3,
      BB6.Agent6ChampionResidual.championP2,
      BB6.Agent6ChampionResidual.championP1,
      BB6.Agent6ChampionResidual.championResidual,
      BB6.Agent6ChampionResidual.championRootAfterB,
      BB6.Agent13BlankDelay.refine,
      BB6Coverage.Agent48Champion.championTable]

/-- Transport the source-checked two-hole parent certificate to the exact
    Agent6 frontier node. -/
theorem parent_certificate_on_championP7 :
    WeightedTNFCertificate championScore championP7 6 := by
  simpa [parent_eq_championP7] using
    BB6.Agent48ChampionCylinder.championParentExactCertificate

/-- Replace the final A/1 split by the complete two-hole A/1–B/1 parent
    certificate. Earlier sibling residuals remain explicit. -/
noncomputable def championFrontierWithParent :
    RootedFrontier championScore championResidual :=
  championStep 0
    (championStep 1
      (championStep 2
        (championStep 3
          (championStep 4
            (championStep 5
              (championStep 6
                (RootedFrontier.closed championP7Path
                  parent_certificate_on_championP7)))))))

theorem championResidualFrontierWithParentSound :
    ∀ m, compatible championResidual m →
      WeightedBound championScore m ∨
        ∃ address q,
          OpenLeaf championFrontierWithParent address q ∧ compatible q m :=
  RootedFrontier.sound championFrontierWithParent

def championResidualFrontierWithParentResiduals :
    List (List Move × PartialMachine) :=
  RootedFrontier.residuals championFrontierWithParent

/-- The final A/1 step contributes 23 unresolved ordinary children in the
    old frontier; the parent certificate closes them, and ten checked
    depth-six F/0 side-cycle witnesses close ten more, leaving 123 open
    residual cylinders (including 13 unresolved F/0 siblings and earlier-depth
    branches). -/
theorem championResidualFrontierWithParentCount :
    championResidualFrontierWithParentResiduals.length = 123 := by
  decide

#print axioms parent_eq_championP7
#print axioms parent_certificate_on_championP7
#print axioms championResidualFrontierWithParentSound
#print axioms championResidualFrontierWithParentCount

/-- The canonical manifest's raw139 address: B0=1RC, then C0=1LD. -/
def championResidualAddress : List Move :=
  [⟨true, true, (2 : Fin 6)⟩, ⟨true, false, (3 : Fin 6)⟩]

/-- Raw139 is exactly present as the champion-containing representative in
    the accepted 78-way quotient roster, not merely quotient-compatible. -/
theorem championResidual_mem_canonical78 :
    (championResidualAddress, championResidual) ∈
      BB6.Agent47Canonical78.roster := by
  decide

/-- Every open leaf of a rooted frontier occurs in its explicit residual list. -/
theorem openLeaf_mem_residuals {B : Nat} {p : PartialMachine}
    {f : RootedFrontier B p} {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) :
    (address, q) ∈ RootedFrontier.residuals f := by
  induction h with
  | here path =>
      simp [RootedFrontier.residuals]
  | @child p n c path hrun hhole hweight children mv address q hchild ih =>
      change (mv :: address, q) ∈
        RootedFrontier.residuals (.expand path hrun hhole hweight children)
      simp only [RootedFrontier.residuals]
      apply List.mem_flatMap.mpr
      refine ⟨mv, allMoves_complete mv, ?_⟩
      apply List.mem_map.mpr
      exact ⟨(address, q), ih, rfl⟩

/-- A frontier whose explicit residual leaves are all covered is itself a
    weighted cover of its root cylinder. -/
theorem cover_of_frontier_leaves {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p)
    (hLeaves : ∀ e ∈ RootedFrontier.residuals f,
      Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) p := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases RootedFrontier.sound f m hm with hB | ⟨address, q, hopen, hq⟩
  · exact hB
  · exact (hLeaves (address, q) (openLeaf_mem_residuals hopen)).sound _ hq

theorem cover_of_championResidual_frontier
    (hLeaves : ∀ e ∈ championResidualFrontierWithParentResiduals,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) championResidual :=
  cover_of_frontier_leaves championFrontierWithParent hLeaves

/-- The exact global composition now needs Covers for the 77 other canonical
    representatives and for the 123 open leaves refining raw139. -/
theorem exact_from_nonchampion_roster_covers_and_parent_frontier
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ championResidualFrontierWithParentResiduals,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent47Canonical78.exact_at_target championScore
    (Nat.le_of_lt BB6.Agent31Canonical78Exact.champion_score_gt_7014)
    (by
      intro e he
      by_cases hEq : e.2 = championResidual
      · simpa [hEq] using cover_of_championResidual_frontier hLeaves
      · exact hOther e he hEq)
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

theorem canonical78_other_address_count :
    (BB6.Agent47Canonical78.roster.filter
      (fun e => e.1 ≠ championResidualAddress)).length = 77 := by
  decide

theorem canonical78_refined_obligation_count :
    (BB6.Agent47Canonical78.roster.filter
      (fun e => e.1 ≠ championResidualAddress)).length +
      championResidualFrontierWithParentResiduals.length = 200 := by
  decide

#print axioms championResidual_mem_canonical78
#print axioms openLeaf_mem_residuals
#print axioms cover_of_frontier_leaves
#print axioms cover_of_championResidual_frontier
#print axioms exact_from_nonchampion_roster_covers_and_parent_frontier
#print axioms canonical78_other_address_count
#print axioms canonical78_refined_obligation_count

end BB6.Agent31ChampionParentIntegration

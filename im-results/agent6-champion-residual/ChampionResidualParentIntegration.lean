import ChampionResidualFrontier
import ChampionParentExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31ChampionParentIntegration

open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier
open BB6.Agent6ChampionResidual

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
    old frontier; the parent certificate closes them, leaving 133 earlier
    sibling cylinders. -/
theorem championResidualFrontierWithParentCount :
    championResidualFrontierWithParentResiduals.length = 133 := by
  decide

#print axioms parent_eq_championP7
#print axioms parent_certificate_on_championP7
#print axioms championResidualFrontierWithParentSound
#print axioms championResidualFrontierWithParentCount

end BB6.Agent31ChampionParentIntegration

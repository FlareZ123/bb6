import Raw112ClosedCover
import PartialWeightExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
The accepted Raw112 parent proof at B = 100000 can be reweighted at any B
without rebuilding its 24 original-source audit shards. The same two remaining
cylinders have unconditional NeverHalts proofs, hence satisfy every B-bound.
PartialWeightExact upgrades the cheap arithmetic checker from sufficient to
necessary. Numerical sharpness needs separate kernel-checked weight facts.
-/

namespace BB6.Agent11Raw112Reweight

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47PartialAudit
open BB6.Agent16ResidualCover BB6.Agent11PartialWeightExact

/-- The very same two accepted *nonhalting* cylinders, polymorphic in B. -/
def acceptedAt (B : Nat) : List (Accepted B) :=
  [nonhalt B BB6Coverage.Agent31Pump.Raw112CarrySweeps.table
      BB6Coverage.Agent31Pump.Raw112CarryRoot.never,
   nonhalt B BB6Coverage.Agent31Pump.Raw112Sibling.sibling
      BB6Coverage.Agent31Pump.Raw112Sibling.never]

/-- Coverage selects exactly the same physical tables at every threshold;
    only the proof fields of Accepted B differ. -/
theorem coveredAt_eq (B : Nat) (p : PartialMachine) :
    covered (acceptedAt B) p =
      covered BB6.Agent47Raw112.accepted p := by rfl

theorem residuals_weighted_at (B : Nat) :
    ∀ e ∈ BB6.Agent47Raw112.residuals,
      ∀ m, compatible e.2 m → WeightedBound B m := by
  intro e he m hm
  have hbase :=
    List.all_eq_true.mp BB6.Agent47Raw112.residuals_covered e he
  have hnew : covered (acceptedAt B) e.2 = true := by
    simpa only [coveredAt_eq] using hbase
  exact covered_sound hnew m hm

/-- For the *complete* Raw112 six-hole cylinder, a uniform B-bound holds
    exactly when the original audit's weight-only traversal passes at B.
    Nothing is assumed of other Canonical39/38 residual representatives. -/
theorem weighted_bound_iff_query_weights (B : Nat) :
    (∀ m, compatible BB6.Agent47Raw112.parent m → WeightedBound B m) ↔
    BB6.Agent32AuditReweight.partialWeights B
      BB6.Agent47Raw112.parent BB6.Agent47Raw112.tree = true := by
  have hres :
      ∀ e ∈ partialResiduals
            BB6.Agent47Raw112.parent BB6.Agent47Raw112.tree,
        ∀ m, compatible e.2 m → WeightedBound B m := by
    simpa [BB6.Agent47Raw112.residuals] using residuals_weighted_at B
  exact partial_weights_exact 100000 B
    BB6.Agent47Raw112.parent BB6.Agent47Raw112.tree
    BB6.Agent47Raw112.parent_root BB6.Agent47Raw112.parent_nohalt
    BB6.Agent47Raw112.checked hres

#print axioms coveredAt_eq
#print axioms residuals_weighted_at
#print axioms weighted_bound_iff_query_weights

end BB6.Agent11Raw112Reweight

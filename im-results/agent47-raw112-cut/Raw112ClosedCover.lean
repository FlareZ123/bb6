import Raw112Data
import Raw112SiblingNever
import ResidualCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw112
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16ResidualCover

def accepted : List (Accepted 100000) :=
  [nonhalt 100000 BB6Coverage.Agent31Pump.Raw112CarrySweeps.table BB6Coverage.Agent31Pump.Raw112CarryRoot.never,
   nonhalt 100000 BB6Coverage.Agent31Pump.Raw112Sibling.sibling BB6Coverage.Agent31Pump.Raw112Sibling.never]

/-- Compare all twelve entries of each actual generated residual table. -/
theorem residuals_covered : residuals.all (fun e => covered accepted e.2) = true := by decide

theorem parent_weighted (m : Machine) (hm : compatible parent m) : WeightedBound 100000 m := by
  rcases sound m hm with hb | ⟨e,he,hc⟩
  · exact hb
  · exact covered_sound (List.all_eq_true.mp residuals_covered e he) m hc

theorem parent_cover : Cover (WeightedBound 100000) parent := .leaf _ parent_weighted

#print axioms residuals_covered
#print axioms parent_cover
end BB6.Agent47Raw112

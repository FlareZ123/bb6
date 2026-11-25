import A6Ingestion
import CanonicalTwoParentRosterOnly

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent48A6Canonical76Ingestion

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier
open BB6.Agent47CanonicalRefinement
open BB6.Agent50TNFPilot

/-- The A6 parent retains the canonical first-one root row. -/
theorem p139_rootRow :
    BB6.Agent19HardRoot.p139 initialSlot =
      some (some ⟨true, true, 1⟩) :=
  BB6.Agent31FourHoleFrontier.RawRootPath.rootRow
    BB6.Agent48A6Ingestion.p139_rawRootPath

/-- The exact A6 parent is still present exactly once after both accepted
raw107 and raw114 cuts; this is the membership bridge into the live 76-roster. -/
theorem p139_parent_count_76 :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => sameTable e.2 BB6.Agent19HardRoot.p139)).length = 1 := by
  decide

/-- Replace only the matching p139 entry of the accepted 76-roster by the
source-connected A6 frontier. Every off-path ordinary sibling remains explicit. -/
noncomputable def A6_refinedRoster76 :
    List (List Move × PartialMachine) :=
  graftRoster BB6.Agent19HardRoot.p139
    BB6.Agent48A6Ingestion.A6_remaining
    BB6.Agent47CanonicalTwoParent.roster76

/-- The 76-parent quotient dichotomy remains sound after the exact A6
source-connected refinement, at the same weighted bound 7014. -/
theorem A6_refinedRoster76_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ A6_refinedRoster76, TNFQuotientCompatible e.2 m := by
  simpa [A6_refinedRoster76] using
    (graftRoster_sound
      (B := 7014)
      (root := BB6.Agent50TNFPilot.root)
      (p := BB6.Agent19HardRoot.p139)
      p139_rootRow
      (BB6.Agent31CanonicalTwoParentRosterOnly.roster76_sound
        BB6.Agent31CanonicalTwoParentRosterOnly.p107_bound
        BB6.Agent31CanonicalTwoParentRosterOnly.p114_bound)
      BB6.Agent48A6Ingestion.A6_remaining_sound)

#print axioms p139_rootRow
#print axioms p139_parent_count_76
#print axioms A6_refinedRoster76
#print axioms A6_refinedRoster76_sound

end BB6.Agent48A6Canonical76Ingestion

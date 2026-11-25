import CanonicalRaw114Accepted
import Raw107ParentClosure
import CanonicalTwoParentGraft

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31CanonicalTwoParentRosterOnly

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- The first parent is exactly the source-certified raw107 table. -/
theorem p107_matches_raw107 :
    BB6.Agent47CanonicalTwoParent.p107 = BB6.Agent10Raw107Root.parent := by
  decide

/-- Instantiate the raw107 parent bound without importing the champion. -/
theorem p107_bound :
    ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m →
      WeightedBound 815 m := by
  intro m hm
  rw [p107_matches_raw107] at hm
  exact BB6.Agent11Raw107ParentClosure.all_completions m hm

/-- Instantiate the independently accepted raw114 parent bound. -/
theorem p114_bound :
    ∀ m, compatible BB6.Agent47CanonicalTwoParent.p114 m →
      WeightedBound 7014 m :=
  BB6.Agent47CanonicalRaw114Accepted.parent_bound

/-- Source-rooted dichotomy after the two exact parent cuts. -/
theorem roster76_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
          TNFQuotientCompatible e.2 m :=
  BB6.Agent47CanonicalTwoParent.roster76_sound p107_bound p114_bound

/-- Generic target-B consumer. The halting witness is an explicit parameter;
    this roster layer has no dependency on the champion-specific source. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
      Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent47CanonicalTwoParent.exact_at_target
    B hB p107_bound p114_bound hLeaves champ

#print axioms p107_matches_raw107
#print axioms p107_bound
#print axioms p114_bound
#print axioms roster76_sound
#print axioms exact_at_target

end BB6.Agent31CanonicalTwoParentRosterOnly

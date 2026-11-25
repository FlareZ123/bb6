import Raw60StableContract
import Raw60RootFull
import CanonicalTwoParentRosterOnly

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw60StableAccepted
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster
open BB6.Agent1Raw60Contract

theorem parent_eq : p60 = BB6.Agent1Raw60Root.parent := by rfl

theorem parent_bound : ∀ m, compatible p60 m → WeightedBound 1175 m := by
  rw [parent_eq]
  exact BB6.Agent1Raw60Root.all60

theorem cover_at_target (B : Nat) (hB : 1175 ≤ B) :
    Cover (WeightedBound B) p60 :=
  raw60_cover hB parent_bound

/-- Exactness with Raw60 discharged against the stable canonical76 base.
Every unmatched entry remains a target-B obligation. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hrest : ∀ e ∈ BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => !(sameTable e.2 p60)), Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent31CanonicalTwoParentRosterOnly.exact_at_target B hB
    (fill_raw60 (by omega) parent_bound hrest) champ

#print axioms parent_eq
#print axioms parent_bound
#print axioms cover_at_target
#print axioms exact_at_target
end BB6.Agent1Raw60StableAccepted

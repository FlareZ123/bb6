import Raw59UpgradeAll
import CanonicalRaw114Accepted

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32Raw59Canonical77

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent31FourHoleRoster

/-- The Raw59 parent survives the already accepted Raw114 cut of the
    canonical 78-entry quotient roster. -/
theorem parent_mem :
    (BB6.Agent32Raw59Partition.address, BB6.Agent32Raw59.p59) ∈
      BB6.Agent47CanonicalRaw114Accepted.roster := by
  change (BB6.Agent32Raw59Partition.address, BB6.Agent32Raw59.p59) ∈
    BB6.Agent47CanonicalRefinement.graftRoster
      BB6.Agent47CanonicalRaw114Accepted.p114 [] BB6.Agent47Canonical78.roster
  decide

/-- The remaining roster after consuming the Raw59 parent bound. -/
noncomputable def remainingRoster :
    List (List Move × PartialMachine) :=
  BB6.Agent47CanonicalRaw114Accepted.roster.filter
    (fun e => !(sameTable e.2 BB6.Agent32Raw59.p59))

theorem remaining_count : remainingRoster.length = 76 := by
  decide

theorem parent_bound_at (B : Nat) (hB : 4200000 ≤ B) :
    ∀ m, compatible BB6.Agent32Raw59.p59 m → WeightedBound B m := by
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent32Raw59UpgradeAll.bound m hm k d hk hd)
    (by omega)

/-- The exact champion theorem now needs Covers only for the 76 entries
    left after the source-checked Raw59 parent is removed. -/
theorem exact_at_target (B : Nat) (hB : 4200000 ≤ B)
    (hLeaves : ∀ e ∈ remainingRoster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  apply BB6.Agent47CanonicalRaw114Accepted.exact_at_target B (by omega) ?_ champ
  intro e he
  by_cases hs : sameTable e.2 BB6.Agent32Raw59.p59 = true
  · have hp : e.2 = BB6.Agent32Raw59.p59 := sameTable_sound hs
    rw [hp]
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent32Raw59UpgradeAll.bound m hm k d hk hd)
      (by omega)
  · have hnot : !(sameTable e.2 BB6.Agent32Raw59.p59) = true := by
      cases h : sameTable e.2 BB6.Agent32Raw59.p59 <;> simp_all
    exact hLeaves e (List.mem_filter.mpr ⟨he, hnot⟩)

#print axioms parent_mem
#print axioms remaining_count
#print axioms parent_bound_at
#print axioms exact_at_target

end BB6.Agent32Raw59Canonical77

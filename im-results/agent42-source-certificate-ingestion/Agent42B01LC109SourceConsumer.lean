import Agent14B01LC109Graft
import HeldBlockRaw10Combined
import MixedBound109Composition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42B01LC109SourceConsumer

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
open BB6.Agent47Combined109 BB6.Agent13MixedBound109
open BB6.Agent14B01LC109Graft BB6.Agent13HeldBlockRaw10Combined
open BB6.Agent17Raw10CombinedConsumer

abbrev B : Nat := championScore
abbrev Parent : PartialMachine := BB6.Agent14B01LC109Graft.Parent

/-- The q2800 held leaf is itself weighted-safe at every B >= 7014. -/
theorem q2800_held_leaf_weighted_at_champion_score :
    ∀ m, compatible BB6.Agent13CrossRouteHeldLeaf109.held m →
      WeightedBound B m :=
  BB6.Agent13HeldBlock.held_weighted B

/-- Four certified families (65 side witnesses, q2800 held leaf, cycle,
    forced halt) plus the exact 41-box complement cover B0=1LC. -/
theorem b0_1lc_parent_cover_from_41_boxes
    (hOpen : ∀ r ∈ raw10RemainderWithCycleAndHalt,
      ∀ m, BB6.Agent49Box.Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) Parent := by
  simpa [Parent, B] using
    BB6.Agent13HeldBlockRaw10Combined.raw10_cover_with_cycle_and_halt
      B (Nat.le_of_lt champion_score_gt_7014) hOpen

/-- Replace the exact B0=1LC member of the 109 roster by its 41 retained
    complement boxes; the other 108 roster entries remain explicit. -/
theorem cover_reduced_roster_from_108_and_41_boxes
    (hOther : ∀ e ∈ otherRoster, Cover (WeightedBound B) e.2)
    (hOpen : ∀ r ∈ raw10RemainderWithCycleAndHalt,
      ∀ m, BB6.Agent49Box.Fits r m → WeightedBound B m) :
    ∀ e ∈ reducedRoster, Cover (WeightedBound B) e.2 := by
  intro e he
  by_cases hsame : sameTable e.2 Parent = true
  · have hEq : e.2 = Parent := sameTable_sound hsame
    rw [hEq]
    exact b0_1lc_parent_cover_from_41_boxes hOpen
  · have hne : e.2 ≠ Parent := by
      intro hEq
      apply hsame
      rw [hEq]
      decide
    exact hOther e (otherRoster_mem_of_ne he hne)

/-- Conditional exact BB(6): only 108 other champion-score residuals and
    41 exact B0=1LC complement boxes remain as premises. -/
theorem exact_from_108_and_41_boxes
    (hOther : ∀ e ∈ otherRoster, Cover (WeightedBound B) e.2)
    (hOpen : ∀ r ∈ raw10RemainderWithCycleAndHalt,
      ∀ m, BB6.Agent49Box.Fits r m → WeightedBound B m) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent13MixedBound109.exact_from_reduced_roster_at_champion_score
    (cover_reduced_roster_from_108_and_41_boxes hOther hOpen)

theorem refined_obligation_count :
    otherRoster.length + raw10RemainderWithCycleAndHalt.length = 149 := by
  rw [BB6.Agent14B01LC109Graft.otherRoster_count,
    BB6.Agent13HeldBlockRaw10Combined.raw10RemainderWithCycleAndHalt_count]
  decide

theorem b0_1lc_mass_conservation :
    BB6.Agent13HeldBlockRaw10Combined.raw10RemainderMass +
      4629927926900 = 95367431640625 := by
  rw [BB6.Agent13HeldBlockRaw10Combined.raw10RemainderWithCycleAndHalt_mass]
  decide

#print axioms BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC_exact_member
#print axioms q2800_held_leaf_weighted_at_champion_score
#print axioms b0_1lc_parent_cover_from_41_boxes
#print axioms cover_reduced_roster_from_108_and_41_boxes
#print axioms exact_from_108_and_41_boxes
#print axioms refined_obligation_count
#print axioms b0_1lc_mass_conservation

end BB6.Agent42B01LC109SourceConsumer

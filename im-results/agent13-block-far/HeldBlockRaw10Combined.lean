import HeldBlockConsumer
import Raw10BoxCombinedConsumer
import Canonical77HeldMembership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13HeldBlockRaw10Combined

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49Box
open BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109

/-- Cardinality of a product box over the twelve transition slots. -/
def boxMass (b : BB6.Agent49Box.Box (Fin 12) (Fin 25)) : Nat :=
  (List.ofFn (fun s : Fin 12 => (b s).length)).prod

/-- Exact finite size of the complement after the 65 side witnesses,
    the q_i(2800,100) held leaf, the 625-completion cycle cylinder, and
    the 25^8 two-step halt cylinder have all been removed. -/
def raw10RemainderMass : Nat :=
  (BB6.Agent17Raw10CombinedConsumer.raw10RemainderWithCycleAndHalt.map boxMass).sum

theorem raw10RemainderWithCycleAndHalt_count :
    BB6.Agent17Raw10CombinedConsumer.raw10RemainderWithCycleAndHalt.length = 41 := by
  decide

theorem raw10RemainderWithCycleAndHalt_mass :
    raw10RemainderMass = 90737503713725 := by
  decide

/-- The parent has ten independent 25-way holes. -/
theorem parent_completion_mass : 25 ^ 10 = 95367431640625 := by
  decide

/-- Exact number of completions removed by the four certified cylinder families. -/
theorem certified_union_mass : 25 ^ 10 - raw10RemainderMass = 4629927926900 := by
  decide

/-- The current four-certificate raw10 cover: side witnesses, held BlockFAR,
    cycle return, and forced-halt leaf. The 41 exact complement boxes remain
    explicit and must still be covered. -/
def raw10_cover_with_cycle_and_halt (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ BB6.Agent17Raw10CombinedConsumer.raw10RemainderWithCycleAndHalt,
      ∀ m, BB6.Agent49Box.Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  BB6.Agent17Raw10CombinedConsumer.raw10CoverWithCycleAndHalt B hB
    (fun m hm => BB6.Agent13HeldBlock.held_weighted B m hm) hOpen

/-- The same B0=1LC parent is a surviving exact member of the current
    post-raw114 77-way canonical roster. -/
theorem parent_in_canonical77 :
    ∃ e ∈ BB6.Agent13Canonical77HeldMembership.canonical77Roster,
      BB6.Agent31FourHoleRoster.sameTable e.2 firstOneB0_1LC = true :=
  BB6.Agent13Canonical77HeldMembership.parent_in_canonical77

#print axioms raw10RemainderWithCycleAndHalt_count
#print axioms raw10RemainderWithCycleAndHalt_mass
#print axioms parent_completion_mass
#print axioms certified_union_mass
#print axioms raw10_cover_with_cycle_and_halt
#print axioms parent_in_canonical77

end BB6.Agent13HeldBlockRaw10Combined

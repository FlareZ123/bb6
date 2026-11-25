import BlockFARBridge
import HeldBlockProof
import Raw10BoxBridge
import WeightedFirstOneCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13HeldBlock
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent13CrossRouteHeldLeaf109 BB6.Agent49BoxBridge BB6.Agent49Box

theorem table_eq : BB6BlockFAR.partialTable BB6BlockFAR.Held.machine = held := by
  funext s
  rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool,
      BB6BlockFAR.partialTable BB6BlockFAR.Held.machine (q,b) = held (q,b) := by decide
  exact h q b

/-- The independently checked forward block certificate proves the actual
    held cylinder nonhalting for every completion, including an assigned
    halt at F1. The original weighted score is unchanged. -/
theorem held_never (m : Machine) (hm : compatible held m) : NeverHalts m :=
  BB6BlockFAR.transfer_never BB6BlockFAR.Held.machine m
    (by rwa [table_eq]) BB6BlockFAR.Held.never

theorem held_weighted (B : Nat) (m : Machine) (hm : compatible held m) :
    WeightedBound B m := weighted_of_never B m (held_never m hm)

def raw10_cover_with_held (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ raw10Remainder, ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  raw10_cover B hB (held_weighted B) hOpen

/-- Canonical 78 score-B contract with the held-leaf premise eliminated.
    Every exact remainder rectangle and other parent remains explicit. -/
theorem exact_from_raw10_block_remainder (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ raw10Remainder, ∀ m, Fits r m → WeightedBound B m)
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ firstOneB0_1LC → Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_raw10_remainder B hB (held_weighted B) hOpen hOther champ

#print axioms table_eq
#print axioms held_never
#print axioms held_weighted
#print axioms raw10_cover_with_held
#print axioms exact_from_raw10_block_remainder
end BB6.Agent13HeldBlock

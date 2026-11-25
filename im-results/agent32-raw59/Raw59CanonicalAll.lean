import Raw59ClosedBranches
import Raw59CanonicalPartition

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59CanonicalAll
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent32Raw59 BB6.Agent32Raw59Partition

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (ho : ∀ e ∈ BB6.Agent47Canonical78.roster, e.2 ≠ p59 → Cover (WeightedBound B) e.2)
    (hr : ∀ mv ∈ retained closed, Cover (WeightedBound B) (child mv))
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent32Raw59Partition.exact_at_target B hB closed closed_sound ho hr champ

#print axioms exact_at_target
end BB6.Agent32Raw59CanonicalAll

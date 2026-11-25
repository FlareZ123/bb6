import Raw59ParentCover
import Raw59CanonicalPartition

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59UpgradeAll
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent32Raw59 BB6.Agent32Raw59Partition

theorem exact_at_target (T : Nat) (hT : B ≤ T)
    (ho : ∀ e ∈ BB6.Agent47Canonical78.roster, e.2 ≠ p59 → Cover (WeightedBound T) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) T) :
    BB6.Coverage.ExactBB6 T := by
  apply BB6.Agent47Canonical78.exact_at_target T (by omega) _ champ
  intro e he
  by_cases eq : e.2 = p59
  · rw [eq]
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (bound m hm k d hk hd) hT
  · exact ho e he eq

#print axioms exact_at_target
end BB6.Agent32Raw59UpgradeAll

import STTransferResidues
import Init.Omega
namespace BB6.Agent9STDistribution
open BB6.Agent9STResidues

/-- Exact number of inputs in one complete mod-243 block with a given
high-level T outgoing tag. -/
def tagCount (t : Nat) : Nat :=
  ((List.range 243).filter (fun m => tTag m = t)).length

theorem exact_counts :
    tagCount 0=81 ∧ tagCount 1=81 ∧ tagCount 2=38 ∧
    tagCount 3=27 ∧ tagCount 4=9 ∧ tagCount 5=7 := by
  decide

#print axioms BB6.Agent9STDistribution.exact_counts
end BB6.Agent9STDistribution

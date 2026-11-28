import D100DelayedTrace
import Run0ExposureBound
import FastZipWeight
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7D100DelayedBound
open BB6Coverage BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent50TNFPilot BB6.Agent7D100ExposureBridge
open BB6.Agent29FastZipWeight
open BB6.Agent7D100Delayed
theorem hroot : table initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem hno : weightedTNFNoAssignedHalt table := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem query : zipRead table 53257978073992275 = some (4,false) := by
  exact zipRead_of_run0 table 53257978073992275 _ reached
theorem hrest : restOK table (4,false) = true := by decide
theorem hweight : weightOK table (4,false) 53257978073992275 53257978073992281 = true :=
  weightOK_of_slack table (4,false) 53257978073992275 53257978073992281 (by omega)
theorem bound (m : Machine) (hm : compatible table m) : WeightedBound 53257978073992281 m :=
  bounded_of_query table 53257978073992275 53257978073992281 (4,false)
    query hroot hno hole hweight hrest m hm
#print axioms bound
end BB6.Agent7D100DelayedBound

import Raw122Late16
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent43Raw122Late16
open BB6Coverage BB6Coverage.Agent29PackedRun BB6Coverage.Agent10ZipAudit
open BB6.Agent10ZipAudit BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent47PartialAudit

def audit : PartialAudit := .closed (.last 1296924 (1,true))
theorem checked : partialCheck 1296926 table audit = true := by
  change zipCheck 1296926 table (.last 1296924 (1,true)) = true
  exact @packed_last table 1296924 1296926 c57 join56 (by decide) (by decide) (by decide)
theorem nohalt_assigned : weightedTNFNoAssignedHalt table := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem bound (m : Machine) (hm : compatible table m) : WeightedBound 1296926 m := by
  rcases partialSound 1296926 table audit (by decide) nohalt_assigned checked m hm with hb | ⟨e,he,hc⟩
  · exact hb
  · rw [audit,partialResiduals.eq_2] at he
    simp at he
#print axioms bound
end BB6Coverage.Agent43Raw122Late16

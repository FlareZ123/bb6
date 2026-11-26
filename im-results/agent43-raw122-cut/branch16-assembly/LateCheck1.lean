import PackedLate1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
theorem last_check : zipCheck 6766859 table (.last 1296924 (1,true)) = true := by
  have h : BB6Coverage.Agent10ZipAudit.zipRead table 1296924 = some (1,true) := packed_read (p:=table) (n:=1296924) (z:=e88) exact_run
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,h]
  decide
theorem bound (m : Machine) (hm : compatible table m) : WeightedBound 6766859 m := by
  have h : partialCheck 6766859 table (.closed (.last 1296924 (1,true))) = true := last_check
  have hn : weightedTNFNoAssignedHalt table := by
    intro ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
  have hs := partialSound 6766859 table (.closed (.last 1296924 (1,true))) (by decide) hn h m hm
  rcases hs with h|⟨e,he,_⟩
  · exact h
  · simp [partialResiduals] at he
#print axioms last_check
#print axioms bound
end BB6Coverage.Agent29PackedLate.M1

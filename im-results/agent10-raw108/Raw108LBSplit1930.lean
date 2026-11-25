import Raw108LongAudit
import Raw108LongAttained
import AuditScore
import Raw108LBSplit1930Kid0
import Raw108LBSplit1930Kid3
import Raw108LBSplit1930Kid6
import Raw108LBSplit1930Kid7
import Raw108LBSplit1930Kid9
import Raw108LBSplit1930Kid11
import Raw108LBSplit1930Kid12
import Raw108LBSplit1930Kid13
import Raw108LBSplit1930Kid15
import Raw108LBSplit1930Kid17
import Raw108LBSplit1930Kid18
import Raw108LBSplit1930Kid19
import Raw108LBSplit1930Kid21
import Raw108LBSplit1930Kid23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw108Split1930
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent8TNFPath
open BB6.Agent31ThreeHole BB6.Agent10Raw108Long

def tree : Audit := .split 91502 (0,true) (byMove [
  .proven BB6.Agent10Raw108LBSplit1930Kid0.table BB6.Agent10Raw108LBSplit1930Kid0.never,
  .last 4136170 (2,true),
  .last 91503 (2,true),
  .proven BB6.Agent10Raw108LBSplit1930Kid3.table BB6.Agent10Raw108LBSplit1930Kid3.never,
  .last 91505 (2,true),
  .last 4136170 (2,true),
  .proven BB6.Agent10Raw108LBSplit1930Kid6.table BB6.Agent10Raw108LBSplit1930Kid6.never,
  .proven BB6.Agent10Raw108LBSplit1930Kid7.table BB6.Agent10Raw108LBSplit1930Kid7.never,
  .last 91503 (2,true),
  .proven BB6.Agent10Raw108LBSplit1930Kid9.table BB6.Agent10Raw108LBSplit1930Kid9.never,
  .last 91505 (2,true),
  .proven BB6.Agent10Raw108LBSplit1930Kid11.table BB6.Agent10Raw108LBSplit1930Kid11.never,
  .proven BB6.Agent10Raw108LBSplit1930Kid12.table BB6.Agent10Raw108LBSplit1930Kid12.never,
  .proven BB6.Agent10Raw108LBSplit1930Kid13.table BB6.Agent10Raw108LBSplit1930Kid13.never,
  .last 91503 (2,true),
  .proven BB6.Agent10Raw108LBSplit1930Kid15.table BB6.Agent10Raw108LBSplit1930Kid15.never,
  .last 91505 (2,true),
  .proven BB6.Agent10Raw108LBSplit1930Kid17.table BB6.Agent10Raw108LBSplit1930Kid17.never,
  .proven BB6.Agent10Raw108LBSplit1930Kid18.table BB6.Agent10Raw108LBSplit1930Kid18.never,
  .proven BB6.Agent10Raw108LBSplit1930Kid19.table BB6.Agent10Raw108LBSplit1930Kid19.never,
  .last 91503 (2,true),
  .proven BB6.Agent10Raw108LBSplit1930Kid21.table BB6.Agent10Raw108LBSplit1930Kid21.never,
  .last 4136174 (2,true),
  .proven BB6.Agent10Raw108LBSplit1930Kid23.table BB6.Agent10Raw108LBSplit1930Kid23.never
])

theorem hroot : table none initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem hno : weightedTNFNoAssignedHalt (table none) := by
  intro s
  rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, table none (q,b) ≠ some none := by decide
  exact h q b

theorem check_ok : BB6.Agent10Raw108FastAudit.zipCheck 4136175 (table none) tree = true := by decide +kernel

theorem upper (m : Machine) (hm : compatible (table none) m) : WeightedBound 4136175 m :=
  (BB6.Agent10Raw108FastAudit.certifiedZip 4136175 (table none) tree hroot hno check_ok).sound m hm

theorem score : BB6.Agent10ExactAuditWeight.auditScore (table none) tree = 4136175 := by decide +kernel

theorem exact_bound (C : Nat) : (∀ m, compatible (table none) m → WeightedBound C m) ↔ 4136175 ≤ C := by
  have h := BB6.Agent10ExactAuditWeight.exact_score_iff (B := 4136175) (C := C) (table none) tree hroot hno
    ((BB6.Agent10Raw108FastAudit.check_eq _ _ _).symm.trans check_ok)
  simpa only [score] using h

#print axioms upper
#print axioms exact_bound
end BB6.Agent10Raw108Split1930

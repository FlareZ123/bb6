import SparseAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3SparseAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6Coverage.Agent13PackedZipper
theorem lateZip_sparse (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (h : zipCheck B p (.last n s) = true) :
    sparseCheck B p (.last n s) = true := by
  change (zipQueryOK B p n s && restOK p s) = true at h
  change (packedQueryOK B p n s && restOK p s) = true
  unfold packedQueryOK zipQueryOK at *
  rw [readRunP_eq]
  exact h
#print axioms lateZip_sparse
end BB6.Agent3SparseAudit

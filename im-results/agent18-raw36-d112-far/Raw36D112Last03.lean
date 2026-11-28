import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent18Raw36D112Last03
open BB6Coverage BB6.Agent31ThreeHole BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6Coverage.FAR
theorem fromCodes_nohalt (xs : List Nat) : weightedTNFNoAssignedHalt (FAR.fromCodes xs) := by
  intro s
  unfold FAR.fromCodes
  cases h : xs[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n =>
      by_cases hn : n < 24
      · simp [h, hn]
      · simp [h, hn]
namespace M18
def p : PartialMachine := FAR.fromCodes [7, 16, 11, 6, 13, 11, 12, 2, 3, 22, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2441 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2441 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M18
namespace M19
def p : PartialMachine := FAR.fromCodes [7, 16, 11, 6, 13, 11, 12, 2, 11, 22, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2451 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2451 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M19
namespace M20
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 6, 13, 11, 12, 2, 0, 20, 24, 15]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2459 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2459 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M20
namespace M21
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 6, 13, 11, 12, 2, 6, 20, 24, 15]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2459 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2459 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M21
namespace M22
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 6, 13, 11, 12, 2, 7, 20, 24, 15]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2469 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2469 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M22
namespace M23
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 6, 13, 11, 12, 2, 13, 20, 24, 15]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2479 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2479 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M23
end BB6.Agent18Raw36D112Last03

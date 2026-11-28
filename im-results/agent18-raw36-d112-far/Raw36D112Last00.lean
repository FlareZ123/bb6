import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent18Raw36D112Last00
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
namespace M0
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 7, 13, 10, 12, 2, 7, 22, 24, 0]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2155 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2155 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M0
namespace M1
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 7, 13, 10, 12, 2, 13, 22, 24, 0]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2165 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2165 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M1
namespace M2
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 7, 13, 10, 12, 2, 9, 22, 24, 0]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2175 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2175 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M2
namespace M3
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 7, 13, 10, 12, 2, 7, 20, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2239 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2239 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M3
namespace M4
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 7, 13, 10, 12, 2, 13, 20, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2249 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2249 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M4
namespace M5
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 7, 13, 10, 12, 2, 21, 20, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2249 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2249 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M5
end BB6.Agent18Raw36D112Last00

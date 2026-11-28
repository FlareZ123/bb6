import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent18Raw36D112Last01
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
namespace M6
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 7, 13, 10, 12, 2, 9, 20, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2259 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2259 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M6
namespace M7
def p : PartialMachine := FAR.fromCodes [7, 16, 11, 7, 13, 10, 12, 2, 3, 22, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2323 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2323 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M7
namespace M8
def p : PartialMachine := FAR.fromCodes [7, 16, 11, 7, 13, 10, 12, 2, 11, 22, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2333 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2333 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M8
namespace M9
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 6, 13, 11, 12, 2, 0, 20, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2337 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2337 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M9
namespace M10
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 6, 13, 11, 12, 2, 6, 20, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2337 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2337 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M10
namespace M11
def p : PartialMachine := FAR.fromCodes [7, 18, 11, 6, 13, 11, 12, 2, 7, 20, 24, 2]
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := fromCodes_nohalt _
theorem checked : zipCheck 2600 p (.last 2347 (5,false)) = true := by decide
noncomputable def cert : WeightedTNFCertificate 2600 p 6 :=
  certifiedZip 2600 p (.last 2347 (5,false)) root nohalt checked
theorem weighted (m : Machine) (hm : compatible p m) : WeightedBound 2600 m :=
  cert.sound m hm
#print axioms checked
#print axioms weighted
end M11
end BB6.Agent18Raw36D112Last01

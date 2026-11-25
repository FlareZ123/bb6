import FastThreeHoleAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48Raw139C1
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit
namespace OneRC
def parent : PartialMachine := fromCodes [7, 24, 11, 24, 14, 11, 3, 16, 12, 11, 24, 24]
def tree : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 4096, 64, 128, 4096, 128, 256, 256, 64, 256, 4096, 4096],[4096, 4096, 256, 256, 256, 4096, 4096, 4096, 256, 256, 256, 4096, 4096],6180⟩
theorem checked : fastCheck 0 parent tree = true := by decide
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ([7, 24, 11, 24, 14, 11, 3, 16, 12, 11, 24, 24] : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate 0 parent 6 :=
  certifiedFast 0 parent tree root nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 0 m := certificate.sound
#print axioms all_completions_weighted
end OneRC
namespace OneRE
def parent : PartialMachine := fromCodes [7, 24, 11, 24, 14, 19, 3, 16, 12, 11, 24, 24]
def tree : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 4096, 64, 128, 4096, 128, 256, 1280, 64, 1280, 4096, 4096],[4096, 4096, 1024, 1280, 256, 4096, 4096, 4096, 1024, 1280, 256, 4096, 4096],6180⟩
theorem checked : fastCheck 0 parent tree = true := by decide
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ([7, 24, 11, 24, 14, 19, 3, 16, 12, 11, 24, 24] : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate 0 parent 6 :=
  certifiedFast 0 parent tree root nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 0 m := certificate.sound
#print axioms all_completions_weighted
end OneRE
end BB6.Agent48Raw139C1

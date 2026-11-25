import FastThreeHoleAudit
import WeightedTNFCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31F1CycleSiblings

open BB6Coverage BB6.Agent10FastAudit BB6.Agent31ThreeHole

/-- No table produced by fromCodes assigns a halt transition. -/
theorem nohalt_fromCodes (xs : List Nat) :
    weightedTNFNoAssignedHalt (fromCodes xs) := by
  intro s
  unfold fromCodes
  cases h : xs[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n =>
    by_cases hn : n < 24 <;> simp [h, hn]

/-- The common first five champion transitions, with one selected F/1 action. -/
def parent0RA : PartialMachine := fromCodes [7,24,11,24,14,21,3,16,12,11,24,1]
def parent0LB : PartialMachine := fromCodes [7,24,11,24,14,21,3,16,12,11,24,4]
def parent1RB : PartialMachine := fromCodes [7,24,11,24,14,21,3,16,12,11,24,7]
def parent0LC : PartialMachine := fromCodes [7,24,11,24,14,21,3,16,12,11,24,8]
def parent1LC : PartialMachine := fromCodes [7,24,11,24,14,21,3,16,12,11,24,10]
def parent1RC : PartialMachine := fromCodes [7,24,11,24,14,21,3,16,12,11,24,11]
def parent0LE : PartialMachine := fromCodes [7,24,11,24,14,21,3,16,12,11,24,16]
def parent1LE : PartialMachine := fromCodes [7,24,11,24,14,21,3,16,12,11,24,18]

/-- Each selected sibling has the same initial transition. -/
theorem root0RA : parent0RA initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem root0LB : parent0LB initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem root1RB : parent1RB initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem root0LC : parent0LC initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem root1LC : parent1LC initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem root1RC : parent1RC initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem root0LE : parent0LE initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem root1LE : parent1LE initialSlot = some (some ⟨true,true,1⟩) := by decide

/-- Turn a checked cycle leaf into a source-level weighted certificate. -/
noncomputable def certificateFor (p : PartialMachine) (tree : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (hcheck : fastCheck 6 p tree = true) :
    WeightedTNFCertificate 6 p 6 :=
  certifiedFast 6 p tree hroot hno hcheck

/-- F/1=0RA (code 1): a 13-step right-translated cycle from the root. -/
def tree0RA : Audit := .cycle 0 13 true (-2)
theorem checked0RA : fastCheck 6 parent0RA tree0RA = true := by decide
noncomputable def certificate0RA : WeightedTNFCertificate 6 parent0RA 6 :=
  certificateFor parent0RA tree0RA root0RA
    (nohalt_fromCodes [7,24,11,24,14,21,3,16,12,11,24,1]) checked0RA
theorem all_completions_weighted0RA :
    ∀ m, compatible parent0RA m → WeightedBound 6 m :=
  certificate0RA.sound

/-- F/1=0LB (code 4): an 18-step left-translated cycle from step 2. -/
def tree0LB : Audit := .cycle 2 18 false 2
theorem checked0LB : fastCheck 6 parent0LB tree0LB = true := by decide
noncomputable def certificate0LB : WeightedTNFCertificate 6 parent0LB 6 :=
  certificateFor parent0LB tree0LB root0LB
    (nohalt_fromCodes [7,24,11,24,14,21,3,16,12,11,24,4]) checked0LB
theorem all_completions_weighted0LB :
    ∀ m, compatible parent0LB m → WeightedBound 6 m :=
  certificate0LB.sound

/-- F/1=1RB (code 7): a 20-step left-translated cycle from step 2. -/
def tree1RB : Audit := .cycle 2 20 false 4
theorem checked1RB : fastCheck 6 parent1RB tree1RB = true := by decide
noncomputable def certificate1RB : WeightedTNFCertificate 6 parent1RB 6 :=
  certificateFor parent1RB tree1RB root1RB
    (nohalt_fromCodes [7,24,11,24,14,21,3,16,12,11,24,7]) checked1RB
theorem all_completions_weighted1RB :
    ∀ m, compatible parent1RB m → WeightedBound 6 m :=
  certificate1RB.sound

/-- F/1=0LC (code 8): a 14-step left-translated cycle from step 2. -/
def tree0LC : Audit := .cycle 2 14 false 2
theorem checked0LC : fastCheck 6 parent0LC tree0LC = true := by decide
noncomputable def certificate0LC : WeightedTNFCertificate 6 parent0LC 6 :=
  certificateFor parent0LC tree0LC root0LC
    (nohalt_fromCodes [7,24,11,24,14,21,3,16,12,11,24,8]) checked0LC
theorem all_completions_weighted0LC :
    ∀ m, compatible parent0LC m → WeightedBound 6 m :=
  certificate0LC.sound

/-- F/1=1LC (code 10): a 14-step left-translated cycle from step 2. -/
def tree1LC : Audit := .cycle 2 14 false 2
theorem checked1LC : fastCheck 6 parent1LC tree1LC = true := by decide
noncomputable def certificate1LC : WeightedTNFCertificate 6 parent1LC 6 :=
  certificateFor parent1LC tree1LC root1LC
    (nohalt_fromCodes [7,24,11,24,14,21,3,16,12,11,24,10]) checked1LC
theorem all_completions_weighted1LC :
    ∀ m, compatible parent1LC m → WeightedBound 6 m :=
  certificate1LC.sound

/-- F/1=1RC (code 11): a 16-step left-translated cycle from step 2. -/
def tree1RC : Audit := .cycle 2 16 false 3
theorem checked1RC : fastCheck 6 parent1RC tree1RC = true := by decide
noncomputable def certificate1RC : WeightedTNFCertificate 6 parent1RC 6 :=
  certificateFor parent1RC tree1RC root1RC
    (nohalt_fromCodes [7,24,11,24,14,21,3,16,12,11,24,11]) checked1RC
theorem all_completions_weighted1RC :
    ∀ m, compatible parent1RC m → WeightedBound 6 m :=
  certificate1RC.sound

/-- F/1=0LE (code 16): a 14-step left-translated cycle from step 2. -/
def tree0LE : Audit := .cycle 2 14 false 2
theorem checked0LE : fastCheck 6 parent0LE tree0LE = true := by decide
noncomputable def certificate0LE : WeightedTNFCertificate 6 parent0LE 6 :=
  certificateFor parent0LE tree0LE root0LE
    (nohalt_fromCodes [7,24,11,24,14,21,3,16,12,11,24,16]) checked0LE
theorem all_completions_weighted0LE :
    ∀ m, compatible parent0LE m → WeightedBound 6 m :=
  certificate0LE.sound

/-- F/1=1LE (code 18): a 14-step left-translated cycle from step 2. -/
def tree1LE : Audit := .cycle 2 14 false 2
theorem checked1LE : fastCheck 6 parent1LE tree1LE = true := by decide
noncomputable def certificate1LE : WeightedTNFCertificate 6 parent1LE 6 :=
  certificateFor parent1LE tree1LE root1LE
    (nohalt_fromCodes [7,24,11,24,14,21,3,16,12,11,24,18]) checked1LE
theorem all_completions_weighted1LE :
    ∀ m, compatible parent1LE m → WeightedBound 6 m :=
  certificate1LE.sound

#print axioms nohalt_fromCodes
#print axioms all_completions_weighted0RA
#print axioms all_completions_weighted0LB
#print axioms all_completions_weighted1RB
#print axioms all_completions_weighted0LC
#print axioms all_completions_weighted1LC
#print axioms all_completions_weighted1RC
#print axioms all_completions_weighted0LE
#print axioms all_completions_weighted1LE

end BB6.Agent31F1CycleSiblings

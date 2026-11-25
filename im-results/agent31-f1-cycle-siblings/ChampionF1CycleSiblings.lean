import FastThreeHoleAudit
import F0SiblingCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31F1CycleSiblings

open BB6Coverage BB6.Agent10FastAudit BB6.Agent31ThreeHole

/-- The raw139 champion-compatible F1 parent with one chosen action. -/
def parent (code : Nat) : PartialMachine :=
  fromCodes [7,24,11,24,14,21,3,16,12,11,24,code]

/-- No table produced by fromCodes assigns a halt transition. -/
theorem nohalt_fromCodes (xs : List Nat) :
    weightedTNFNoAssignedHalt (fromCodes xs) := by
  intro s
  unfold fromCodes
  cases h : xs[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n =>
    by_cases hn : n < 24 <;> simp [h, hn]

/-- Every sibling has the same five-step champion prefix and root. -/
theorem root (code : Nat) :
    parent code initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- A cycle audit at bound six gives a complete weighted cover. -/
noncomputable def certificate (code : Nat) (tree : Audit)
    (hcheck : fastCheck 6 (parent code) tree = true) :
    WeightedTNFCertificate 6 (parent code) 6 :=
  certifiedFast 6 (parent code) tree (root code)
    (nohalt_fromCodes [7,24,11,24,14,21,3,16,12,11,24,code]) hcheck

theorem all_completions_weighted (code : Nat) (tree : Audit)
    (hcheck : fastCheck 6 (parent code) tree = true) :
    ∀ m, compatible (parent code) m → WeightedBound 6 m :=
  (certificate code tree hcheck).sound

/-- F/1=0RA (code 1): a 13-step right-translated cycle from the root. -/
def tree0RA : Audit := .cycle 0 13 true (-2)
theorem checked0RA : fastCheck 6 (parent 1) tree0RA = true := by decide
theorem all_completions_weighted0RA :
    ∀ m, compatible (parent 1) m → WeightedBound 6 m :=
  all_completions_weighted 1 tree0RA checked0RA

/-- F/1=0LB (code 4): a 18-step left-translated cycle from step 2. -/
def tree0LB : Audit := .cycle 2 18 false 2
theorem checked0LB : fastCheck 6 (parent 4) tree0LB = true := by decide
theorem all_completions_weighted0LB :
    ∀ m, compatible (parent 4) m → WeightedBound 6 m :=
  all_completions_weighted 4 tree0LB checked0LB

/-- F/1=1RB (code 7): a 20-step left-translated cycle from step 2. -/
def tree1RB : Audit := .cycle 2 20 false 4
theorem checked1RB : fastCheck 6 (parent 7) tree1RB = true := by decide
theorem all_completions_weighted1RB :
    ∀ m, compatible (parent 7) m → WeightedBound 6 m :=
  all_completions_weighted 7 tree1RB checked1RB

/-- F/1=0LC (code 8): a 14-step left-translated cycle from step 2. -/
def tree0LC : Audit := .cycle 2 14 false 2
theorem checked0LC : fastCheck 6 (parent 8) tree0LC = true := by decide
theorem all_completions_weighted0LC :
    ∀ m, compatible (parent 8) m → WeightedBound 6 m :=
  all_completions_weighted 8 tree0LC checked0LC

/-- F/1=1LC (code 10): a 14-step left-translated cycle from step 2. -/
def tree1LC : Audit := .cycle 2 14 false 2
theorem checked1LC : fastCheck 6 (parent 10) tree1LC = true := by decide
theorem all_completions_weighted1LC :
    ∀ m, compatible (parent 10) m → WeightedBound 6 m :=
  all_completions_weighted 10 tree1LC checked1LC

/-- F/1=1RC (code 11): a 16-step left-translated cycle from step 2. -/
def tree1RC : Audit := .cycle 2 16 false 3
theorem checked1RC : fastCheck 6 (parent 11) tree1RC = true := by decide
theorem all_completions_weighted1RC :
    ∀ m, compatible (parent 11) m → WeightedBound 6 m :=
  all_completions_weighted 11 tree1RC checked1RC

/-- F/1=0LE (code 16): a 14-step left-translated cycle from step 2. -/
def tree0LE : Audit := .cycle 2 14 false 2
theorem checked0LE : fastCheck 6 (parent 16) tree0LE = true := by decide
theorem all_completions_weighted0LE :
    ∀ m, compatible (parent 16) m → WeightedBound 6 m :=
  all_completions_weighted 16 tree0LE checked0LE

/-- F/1=1LE (code 18): a 14-step left-translated cycle from step 2. -/
def tree1LE : Audit := .cycle 2 14 false 2
theorem checked1LE : fastCheck 6 (parent 18) tree1LE = true := by decide
theorem all_completions_weighted1LE :
    ∀ m, compatible (parent 18) m → WeightedBound 6 m :=
  all_completions_weighted 18 tree1LE checked1LE

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

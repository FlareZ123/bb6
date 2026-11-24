import WeightedTNFBridge
import FreshRayGlider

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- A one-state left DFA and a right NFA for the four-step fresh-cell
    glider. Nodes 0,1,2 are controls A,B,C; 3,4,5 are unreachable controls;
    6 is the halt sink. -/
def gliderFARData : FAR.Data 1 :=
  ⟨0, [0, 0],
    [2, 1, 1, 64, 64, 64, 64],
    [4, 64, 64, 64, 64, 64, 64],
    120⟩

theorem gliderFARValid : gliderFARData.fastValid gliderExample = true := by
  decide

theorem gliderRoot :
    gliderExample initialSlot = some (some ⟨true, true, 1⟩) := by
  simp [initialSlot, gliderExample]

theorem gliderSupport : TNFSupport gliderExample 3 := by
  intro s t h
  rcases s with ⟨q, a⟩
  fin_cases q <;> cases a <;>
    simp [gliderExample] at h <;>
    cases t with
    | none => simp [gliderExample] at h
    | some mv =>
      simp [gliderExample] at h
      cases h
      constructor <;> simp

theorem gliderNoAssignedHalt :
    weightedTNFNoAssignedHalt gliderExample := by
  intro s h
  rcases s with ⟨q, a⟩
  fin_cases q <;> cases a <;> simp [gliderExample] at h

/-- A concrete weighted-TNF nonhalting leaf built from an explicit
    one-state FAR certificate, not from the FAR search procedure. -/
def gliderFARTNFLeaf (B : Nat) :
    WeightedTNFCertificate B gliderExample 3 :=
  farDataNonhaltLeaf gliderRoot gliderSupport gliderNoAssignedHalt
    gliderFARData gliderFARValid

#print axioms gliderFARValid
#print axioms gliderFARTNFLeaf
end BB6.Agent13BlankDelay

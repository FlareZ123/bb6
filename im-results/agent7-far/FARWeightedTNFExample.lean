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
  classical
  intro s t ht
  by_cases h0 : s = (0,false)
  · subst s
    have ht' : t = some ⟨true,true,1⟩ := by
      simpa [gliderExample] using ht.symm
    subst t
    constructor
    · simp
    · intro mv hm
      have hmv : (⟨true,true,1⟩ : Move) = mv := Option.some.inj hm
      subst mv
      simp
  · by_cases h1 : s = (1,false)
    · subst s
      have ht' : t = some ⟨false,false,0⟩ := by
        simpa [gliderExample] using ht.symm
      subst t
      constructor
      · simp
      · intro mv hm
        have hmv : (⟨false,false,0⟩ : Move) = mv := Option.some.inj hm
        subst mv
        simp
    · by_cases h2 : s = (0,true)
      · subst s
        have ht' : t = some ⟨false,true,2⟩ := by
          simpa [gliderExample] using ht.symm
        subst t
        constructor
        · simp
        · intro mv hm
          have hmv : (⟨false,true,2⟩ : Move) = mv := Option.some.inj hm
          subst mv
          simp
      · by_cases h3 : s = (2,false)
        · subst s
          have ht' : t = some ⟨false,true,0⟩ := by
            simpa [gliderExample] using ht.symm
          subst t
          constructor
          · simp
          · intro mv hm
            have hmv : (⟨false,true,0⟩ : Move) = mv := Option.some.inj hm
            subst mv
            simp
        · simp [gliderExample, h0, h1, h2, h3] at ht

theorem gliderNoAssignedHalt :
    weightedTNFNoAssignedHalt gliderExample := by
  classical
  intro s
  by_cases h0 : s = (0,false)
  · subst s
    simp [gliderExample]
  · by_cases h1 : s = (1,false)
    · subst s
      simp [gliderExample]
    · by_cases h2 : s = (0,true)
      · subst s
        simp [gliderExample]
      · by_cases h3 : s = (2,false)
        · subst s
          simp [gliderExample]
        · simp [gliderExample, h0, h1, h2, h3]

/-- A concrete weighted-TNF nonhalting leaf built from an explicit
    one-state FAR certificate, not from the FAR search procedure. -/
def gliderFARTNFLeaf (B : Nat) :
    WeightedTNFCertificate B gliderExample 3 :=
  farDataNonhaltLeaf gliderRoot gliderSupport gliderNoAssignedHalt
    gliderFARData gliderFARValid

#print axioms gliderFARValid
#print axioms gliderFARTNFLeaf
end BB6.Agent13BlankDelay

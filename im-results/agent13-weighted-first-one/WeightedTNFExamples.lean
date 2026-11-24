import WeightedTNFCertificate
import FreshRayGlider

namespace BB6.Agent13BlankDelay

open BB6Coverage

/-- A concrete non-singleton firstOne residual already covered by Agent 6's
    three-step fresh-frontier glider theorem. Its only assigned rows are
    A/0=1RB, B/0=0LC, and C/1=0RA; the remaining nine rows are free. -/
abbrev threeGliderTNFNode : PartialMachine :=
  BB6Coverage.threeGliderExample

theorem threeGliderTNF_root :
    threeGliderTNFNode initialSlot = some (some ⟨true, true, 1⟩) := by
  simp [threeGliderTNFNode, BB6Coverage.threeGliderExample, initialSlot]

theorem threeGliderTNF_support :
    TNFSupport threeGliderTNFNode 3 := by
  classical
  intro s t ht
  by_cases h0 : s = (0,false)
  · subst s
    have ht' : t = some ⟨true,true,1⟩ := by
      simpa [threeGliderTNFNode, BB6Coverage.threeGliderExample] using ht.symm
    subst t
    constructor
    · simp
    · intro mv hm
      have hmv : (⟨true,true,1⟩ : Move) = mv := Option.some.inj hm
      subst mv
      simp
  · by_cases h1 : s = (1,false)
    · subst s
      have ht' : t = some ⟨false,false,2⟩ := by
        simpa [threeGliderTNFNode, BB6Coverage.threeGliderExample] using ht.symm
      subst t
      constructor
      · simp
      · intro mv hm
        have hmv : (⟨false,false,2⟩ : Move) = mv := Option.some.inj hm
        subst mv
        simp
    · by_cases h2 : s = (2,true)
      · subst s
        have ht' : t = some ⟨false,true,0⟩ := by
          simpa [threeGliderTNFNode, BB6Coverage.threeGliderExample] using ht.symm
        subst t
        constructor
        · simp
        · intro mv hm
          have hmv : (⟨false,true,0⟩ : Move) = mv := Option.some.inj hm
          subst mv
          simp
      · simp [threeGliderTNFNode, BB6Coverage.threeGliderExample, h0, h1, h2] at ht

theorem threeGliderTNF_noAssignedHalt :
    weightedTNFNoAssignedHalt threeGliderTNFNode := by
  classical
  intro s
  by_cases h0 : s = (0,false)
  · subst s
    simp [threeGliderTNFNode, BB6Coverage.threeGliderExample]
  · by_cases h1 : s = (1,false)
    · subst s
      simp [threeGliderTNFNode, BB6Coverage.threeGliderExample]
    · by_cases h2 : s = (2,true)
      · subst s
        simp [threeGliderTNFNode, BB6Coverage.threeGliderExample]
      · simp [threeGliderTNFNode, BB6Coverage.threeGliderExample, h0, h1, h2]

theorem threeGliderTNF_never :
    ∀ m, compatible threeGliderTNFNode m → NeverHalts m := by
  intro m hm
  apply BB6Coverage.three_glider_never m 1 2 false
  have hp : BB6Coverage.PartialThreeGlider 1 2 false threeGliderTNFNode := by
    simp [threeGliderTNFNode, BB6Coverage.threeGliderExample,
      BB6Coverage.PartialThreeGlider]
  exact ⟨hm _ _ hp.1, hm _ _ hp.2.1, hm _ _ hp.2.2⟩

/-- A closed TNF leaf at cut 3, covering all 25^9 completions. -/
def threeGliderTNFCertificate (B : Nat) :
    WeightedTNFCertificate B threeGliderTNFNode 3 :=
  WeightedTNFCertificate.ofNonhaltCover
    threeGliderTNF_root
    threeGliderTNF_support
    threeGliderTNF_noAssignedHalt
    (.leaf threeGliderTNFNode threeGliderTNF_never)

/-- Every compatible completion of the three-row cylinder is weighted
    below any bound, because its blank run is infinite. -/
theorem threeGliderTNFCertificate_sound (B : Nat) :
    ∀ m, compatible threeGliderTNFNode m → WeightedBound B m :=
  (threeGliderTNFCertificate B).sound

#print axioms threeGliderTNF_root
#print axioms threeGliderTNF_support
#print axioms threeGliderTNF_noAssignedHalt
#print axioms threeGliderTNF_never
#print axioms threeGliderTNFCertificate
#print axioms threeGliderTNFCertificate_sound

end BB6.Agent13BlankDelay

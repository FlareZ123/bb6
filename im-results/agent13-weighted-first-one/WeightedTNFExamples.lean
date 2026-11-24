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


/-- A second, 25-completion cylinder exercises the weighted last-hole rule:
all rows except B/0 are ordinary, and B/0 is the only remaining hole. -/
def lastHoleTNFNode : PartialMachine := fun s =>
  if s = initialSlot then some (some ⟨true,true,1⟩)
  else if s = (1,false) then none
  else some (some ⟨false,false,0⟩)

def lastHoleTNFConfig : Config :=
  applyMove blank ⟨true,true,1⟩

theorem lastHoleTNF_root :
    lastHoleTNFNode initialSlot = some (some ⟨true,true,1⟩) := by
  simp [lastHoleTNFNode, initialSlot]

theorem lastHoleTNF_run :
    knownRun lastHoleTNFNode 1 = some lastHoleTNFConfig := by
  simp [knownRun, knownStep, lastHoleTNFNode, lastHoleTNFConfig,
    initialSlot, readSlot, applyMove, blank]

theorem lastHoleTNF_read :
    readSlot lastHoleTNFConfig = (1,false) := by
  simp [lastHoleTNFConfig, readSlot, applyMove, blank]

theorem lastHoleTNF_hole :
    lastHoleTNFNode (readSlot lastHoleTNFConfig) = none := by
  rw [lastHoleTNF_read]
  simp [lastHoleTNFNode, initialSlot]

theorem lastHoleTNF_support :
    TNFSupport lastHoleTNFNode 6 := by
  classical
  intro s t ht
  constructor
  · exact s.1.isLt
  · intro mv hm
    by_cases h0 : s = initialSlot
    · subst s
      have ht' : t = some ⟨true,true,1⟩ := by
        simpa [lastHoleTNFNode, initialSlot] using ht.symm
      subst t
      have hmv : (⟨true,true,1⟩ : Move) = mv := Option.some.inj hm
      subst mv
      simp
    · by_cases h1 : s = (1,false)
      · subst s
        simp [lastHoleTNFNode, initialSlot] at ht
      · have ht' : t = some ⟨false,false,0⟩ := by
          simpa [lastHoleTNFNode, initialSlot, h0, h1] using ht.symm
        subst t
        have hmv : (⟨false,false,0⟩ : Move) = mv := Option.some.inj hm
        subst mv
        simp

theorem lastHoleTNF_noAssignedHalt :
    weightedTNFNoAssignedHalt lastHoleTNFNode := by
  classical
  intro s
  by_cases h0 : s = initialSlot
  · subst s
    simp [lastHoleTNFNode, initialSlot]
  · by_cases h1 : s = (1,false)
    · subst s
      simp [lastHoleTNFNode, initialSlot]
    · simp [lastHoleTNFNode, initialSlot, h0, h1]

theorem lastHoleTNF_rest :
    ∀ s, s ≠ readSlot lastHoleTNFConfig →
      ∃ mv, lastHoleTNFNode s = some (some mv) := by
  intro s hs
  have hr := lastHoleTNF_read
  by_cases h0 : s = initialSlot
  · subst s
    exact ⟨⟨true,true,1⟩, by simp [lastHoleTNFNode, initialSlot]⟩
  · by_cases h1 : s = (1,false)
    · subst s
      exact False.elim (hs hr)
    · exact ⟨⟨false,false,0⟩,
        by simp [lastHoleTNFNode, initialSlot, h0, h1]⟩

theorem lastHoleTNF_weight :
    ∀ d ∈ possibleDelays
      (refine lastHoleTNFNode (readSlot lastHoleTNFConfig) none) 0,
      d + 1 + 1 ≤ 7 := by
  intro d hd
  have hm : d ∈ List.range 6 := (List.mem_filter.mp hd).1
  have hlt : d < 6 := List.mem_range.mp hm
  omega

/-- The 25 completions of this last-hole cylinder are all weighted below 7:
    24 ordinary choices make a total all-ordinary table; halt is bounded by
    the exact delay list and the one-step known run. -/
def lastHoleTNFCertificate :
    WeightedTNFCertificate 7 lastHoleTNFNode 6 :=
  .lastHole lastHoleTNF_root lastHoleTNF_support (by omega)
    1 lastHoleTNFConfig lastHoleTNF_run lastHoleTNF_hole
    lastHoleTNF_rest lastHoleTNF_weight

theorem lastHoleTNFCertificate_sound :
    ∀ m, compatible lastHoleTNFNode m → WeightedBound 7 m :=
  lastHoleTNFCertificate.sound

#print axioms threeGliderTNF_root
#print axioms threeGliderTNF_support
#print axioms threeGliderTNF_noAssignedHalt
#print axioms threeGliderTNF_never
#print axioms threeGliderTNFCertificate
#print axioms threeGliderTNFCertificate_sound
#print axioms lastHoleTNFCertificate
#print axioms lastHoleTNFCertificate_sound

end BB6.Agent13BlankDelay

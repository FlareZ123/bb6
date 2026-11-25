import RootFrontier
import TranslatedCycler

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent24Q32SourceSideGraft

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent32FiniteSource
open BB6.Agent50TNFPilot
open BB6.Agent50RootFrontier
open BB6.Agent50TranslatedCycler

/-- The eight ordinary first-hole refinements from the q32 source checkpoint
    to its first SWside cylinder. The source table is
    1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------. -/
def samplePath : List PathEntry :=
  [(1, (1,false), ⟨true,true,2⟩),
   (2, (2,false), ⟨false,false,0⟩),
   (3, (0,true), ⟨true,true,3⟩),
   (4, (3,false), ⟨true,false,0⟩),
   (6, (3,true), ⟨false,false,1⟩),
   (7, (1,true), ⟨true,false,1⟩),
   (10, (2,true), ⟨false,false,4⟩),
   (11, (4,true), ⟨true,false,0⟩)]

/-- Each entry is the actual first undefined query, not merely a table
    extension. The halt sibling at every edge is within score 84. -/
theorem samplePathOK : pathOK84 root 2 samplePath = true := by
  decide

/-- The path endpoint is exactly the partial table serialized in the
    original-source q32 checkpoint and in the SWside witness roster. -/
theorem samplePathEnd_table :
    (pathEnd root 2 samplePath).1 = samplePartial := by
  apply packTable_injective
  decide

theorem samplePathEnd_cut : (pathEnd root 2 samplePath).2 = 5 := by
  decide

theorem sampleSourceEncoding :
    encodeTable samplePartial =
      "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------" := by
  decide

/-- The left-oriented SWside L 7 6 0 witness is independently replayed by
    the Lean translated-cycler checker and consumed as a score-84 TNF leaf. -/
def sampleCertificate :
    WeightedTNFCertificate 84 (pathEnd root 2 samplePath).1 6 := by
  rw [samplePathEnd_table]
  exact sampleSourceLeaf 84

/-- Keep all 24 ordinary siblings at each first-hole split, but close the
    exact q32/SWside branch with the independently checked TNF certificate. -/
def sampleFrontier : RootedFrontier 84 root :=
  buildFrontier root 2 RawRootPath.root samplePath samplePathOK sampleCertificate

theorem sampleFrontier_sound :
    ∀ m, compatible root m →
      WeightedBound 84 m ∨
        ∃ address q, OpenLeaf sampleFrontier address q ∧ compatible q m :=
  RootedFrontier.sound sampleFrontier

theorem sampleSourceLeaf_sound (m : Machine)
    (hm : compatible samplePartial m) : WeightedBound 84 m :=
  (sampleSourceLeaf 84).sound m hm

/-- The sample path is a closed leaf, not an open residual in the exported
    exact manifest. This is a finite kernel computation over packed tables. -/
def samplePathAddress : List Move :=
  [⟨true,true,2⟩,
   ⟨false,false,0⟩,
   ⟨true,true,3⟩,
   ⟨true,false,0⟩,
   ⟨false,false,1⟩,
   ⟨true,false,1⟩,
   ⟨false,false,4⟩,
   ⟨true,false,0⟩]

theorem sampleSourceCylinder_removed :
    (samplePathAddress, packTable samplePartial) ∉
      packResiduals (residuals sampleFrontier) := by
  decide

theorem sampleFrontier_residual_count :
    (residuals sampleFrontier).length = 184 := by
  decide

#print axioms samplePathOK
#print axioms sampleCertificate
#print axioms sampleFrontier_sound
#print axioms sampleSourceCylinder_removed

end BB6.Agent24Q32SourceSideGraft

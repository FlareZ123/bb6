import ChampionRootBridge

/-!
# Finite root-to-initial-S1 computation

A kernel-checkable finite run of the exact TM2 table from blank state 0.
The output marked-list order is the order produced by fMove, not a
sorted-set normalization. The source-S1 tape embedding is proved separately.
-/

namespace BB6Coverage.Agent42InitialS1Root

open BB6Coverage.Agent48Champion

def initialS1Marks : List Int :=
  [31, 32, 33] ++
    (List.range 192).map (fun i => (36 + i : Int)) ++
    (List.range 18).map (fun i => (29 - i : Int)) ++
    [11, 10, 8, 5, 2, -1, -4, -5, -6, -8, -9, -10]

def initialS1Finite : FConfig :=
  ⟨3, 29, initialS1Marks⟩

/-- Exact finite TM2 run from the blank state-0 root to the initial S1 tape. -/
theorem tm2_blank_reaches_initialS1_finite :
    fRun tm2 27959 (fBlankAt 0) = some initialS1Finite := by
  decide

end BB6Coverage.Agent42InitialS1Root

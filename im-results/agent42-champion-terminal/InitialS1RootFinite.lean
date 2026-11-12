import ChampionRootBridge
import S1Encoder

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


open BB6Coverage.Agent8S1Encoder

/-- The ascending source-tape support on the interval [-40,227]. -/
def initialS1Support : List Int :=
  ((List.range 268).map (fun i => (i : Int) - 40)).filter
    (fun x => (s1Config 3 7 2 6 0 63 29).tape x)

/-- The finite-run output and the S1 source tape have the same marked cells
    throughout an interval containing the complete source support. -/
theorem tm2_initialS1_marks_perm :
    initialS1Marks.Perm initialS1Support := by
  decide

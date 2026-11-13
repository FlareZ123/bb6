import Low43Delta
import W4HeadMax
import W4HeadPrefix
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low43Continuation

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429Low3Delta BB429Low43Delta
open BB429W4HeadMax BB429W4HeadPrefix

/-- The concrete v=5,k=7 low-43 C/0 context has a 438-step exact
    continuation to J(23,18). The 119-step Junc(0,9,25) candidate was
    incorrect: tens 14 has 28 bits, not 14. -/
theorem root_low43_C0_to_junc_max :
    runWithMax 438
      (z 2 (true::false::true::true::
        (ones 26 ++ (tens 14 ++ ones 6))) false []) =
      some (junc 23 0 18, -20, 1) := by
  decide

theorem root_low43_C0_to_junc :
    runWithDelta 438
      (z 2 (true::false::true::true::
        (ones 26 ++ (tens 14 ++ ones 6))) false []) =
      some (junc 23 0 18, -20) := by
  simpa [root_low43_C0_to_junc_max] using
    ((runWithMax_toDelta 438
      (z 2 (true::false::true::true::
        (ones 26 ++ (tens 14 ++ ones 6))) false [])).symm)

/-- The next exact root-relevant prepared return, from J(23,18) to
    J(11,62), including the complete prefix maximum. -/
theorem root_low43_junc23_to_junc11_max :
    runWithMax 909 (junc 23 0 18) =
      some (junc 11 0 62, -37, 28) := by
  decide

/-- Compose the two concrete monitors. From the low-43 C/0 checkpoint
    the 1347-step continuation reaches J(11,62), with net displacement
    -57 and maximum rightward displacement +8. -/
theorem root_low43_C0_to_junc11_max :
    runWithMax 1347
      (z 2 (true::false::true::true::
        (ones 26 ++ (tens 14 ++ ones 6))) false []) =
      some (junc 11 0 62, -57, 8) := by
  have h1 : runWithMax 438
      (z 2 (true::false::true::true::
        (ones 26 ++ (tens 14 ++ ones 6))) false []) =
      some (junc 23 0 18, -20, 1) :=
    root_low43_C0_to_junc_max
  have h2 : runWithMax 909 (junc 23 0 18) =
      some (junc 11 0 62, -37, 28) :=
    root_low43_junc23_to_junc11_max
  have ht : 438+909=1347 := by omega
  rw [← ht, runWithMax_add, h1]
  simp [h2, Int.max_def]

theorem root_low43_C0_to_junc11 :
    runWithDelta 1347
      (z 2 (true::false::true::true::
        (ones 26 ++ (tens 14 ++ ones 6))) false []) =
      some (junc 11 0 62, -57) := by
  simpa [root_low43_C0_to_junc11_max] using
    ((runWithMax_toDelta 1347
      (z 2 (true::false::true::true::
        (ones 26 ++ (tens 14 ++ ones 6))) false [])).symm)


/-- A concrete prepared low-even return on the simulated root route:
    J(49,2) has deficit 96=4*24 and reaches J(11,98) in 719 moves. -/
theorem root_low_even_r96_max :
    runWithMax 719 (junc 49 0 2) =
      some (junc 11 0 98, -89, 12) := by
  decide

theorem root_low_even_r96 :
    runWithDelta 719 (junc 49 0 2) =
      some (junc 11 0 98, -89) := by
  simpa [root_low_even_r96_max] using
    ((runWithMax_toDelta 719 (junc 49 0 2)).symm)


/-- The next prepared root-route high-three branch, J(11,62) -> J(25,37). -/
theorem root_junc11_to_junc25_max :
    runWithMax 621 (junc 11 0 62) =
      some (junc 25 0 37, 25, 25) := by
  decide

/-- Concrete low-odd return at v=18,n=2: J(25,37) -> J(10,74).
    This finite monitor includes the full prefix maximum, not only the
    first C/0 record. -/
theorem root_lowodd_junc25_to_junc10_max :
    runWithMax 1836 (junc 25 0 37) =
      some (junc 10 0 74, -34, 43) := by
  decide

/-- Compose the two prepared transitions. From J(11,62), the 2457-step
    route reaches J(10,74), with displacement -9 and maximum +68. -/
theorem root_junc11_to_junc10_max :
    runWithMax 2457 (junc 11 0 62) =
      some (junc 10 0 74, -9, 68) := by
  have h1 : runWithMax 621 (junc 11 0 62) =
      some (junc 25 0 37, 25, 25) := root_junc11_to_junc25_max
  have h2 : runWithMax 1836 (junc 25 0 37) =
      some (junc 10 0 74, -34, 43) :=
    root_lowodd_junc25_to_junc10_max
  have ht : 621+1836=2457 := by omega
  rw [← ht, runWithMax_add, h1]
  simp [h2, Int.max_def]

theorem root_junc11_to_junc10 :
    runWithDelta 2457 (junc 11 0 62) =
      some (junc 10 0 74, -9) := by
  simpa [root_junc11_to_junc10_max] using
    ((runWithMax_toDelta 2457 (junc 11 0 62)).symm)


/-- First high-three branch from J(10,74) to J(23,51). -/
theorem root_junc10_to_junc23_max :
    runWithMax 527 (junc 10 0 74) =
      some (junc 23 0 51, 23, 23) := by
  decide

/-- Second high-three branch from J(23,51) to J(49,2). -/
theorem root_junc23_to_junc49_max :
    runWithMax 2373 (junc 23 0 51) =
      some (junc 49 0 2, 49, 49) := by
  decide

/-- Compose the two high-three branches. -/
theorem root_junc10_to_junc49_max :
    runWithMax 2900 (junc 10 0 74) =
      some (junc 49 0 2, 72, 72) := by
  have h1 : runWithMax 527 (junc 10 0 74) =
      some (junc 23 0 51, 23, 23) := root_junc10_to_junc23_max
  have h2 : runWithMax 2373 (junc 23 0 51) =
      some (junc 49 0 2, 49, 49) := root_junc23_to_junc49_max
  have ht : 527+2373=2900 := by omega
  rw [← ht, runWithMax_add, h1]
  simp [h2, Int.max_def]

/-- Continue through the concrete low-even r=96 return J(49,2)->J(11,98).
    The complete 3619-step J(10,74) branch has displacement -17 and
    maximum +84. -/
theorem root_junc10_to_junc11_r96_max :
    runWithMax 3619 (junc 10 0 74) =
      some (junc 11 0 98, -17, 84) := by
  have h1 : runWithMax 2900 (junc 10 0 74) =
      some (junc 49 0 2, 72, 72) := root_junc10_to_junc49_max
  have h2 : runWithMax 719 (junc 49 0 2) =
      some (junc 11 0 98, -89, 12) := root_low_even_r96_max
  have ht : 2900+719=3619 := by omega
  rw [← ht, runWithMax_add, h1]
  simp [h2, Int.max_def]

theorem root_junc10_to_junc11_r96 :
    runWithDelta 3619 (junc 10 0 74) =
      some (junc 11 0 98, -17) := by
  simpa [root_junc10_to_junc11_r96_max] using
    ((runWithMax_toDelta 3619 (junc 10 0 74)).symm)

#print axioms root_low43_C0_to_junc_max
#print axioms root_low43_C0_to_junc
#print axioms root_low43_junc23_to_junc11_max
#print axioms root_low43_C0_to_junc11_max
#print axioms root_low43_C0_to_junc11
#print axioms root_low_even_r96_max
#print axioms root_low_even_r96
#print axioms root_junc11_to_junc25_max
#print axioms root_lowodd_junc25_to_junc10_max
#print axioms root_junc11_to_junc10_max
#print axioms root_junc11_to_junc10
#print axioms root_junc10_to_junc23_max
#print axioms root_junc23_to_junc49_max
#print axioms root_junc10_to_junc49_max
#print axioms root_junc10_to_junc11_r96_max
#print axioms root_junc10_to_junc11_r96

end BB429Low43Continuation

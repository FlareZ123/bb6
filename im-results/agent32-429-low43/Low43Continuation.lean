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
        (ones 26 ++ tens 14 ++ ones 6)) false []) =
      some (junc 23 0 18, -20, 1) := by
  decide

theorem root_low43_C0_to_junc :
    runWithDelta 438
      (z 2 (true::false::true::true::
        (ones 26 ++ tens 14 ++ ones 6)) false []) =
      some (junc 23 0 18, -20) := by
  simpa [root_low43_C0_to_junc_max] using
    (runWithMax_toDelta 438
      (z 2 (true::false::true::true::
        (ones 26 ++ tens 14 ++ ones 6)) false []))

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
        (ones 26 ++ tens 14 ++ ones 6)) false []) =
      some (junc 11 0 62, -57, 8) := by
  have h1 : runWithMax 438
      (z 2 (true::false::true::true::
        (ones 26 ++ tens 14 ++ ones 6)) false []) =
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
        (ones 26 ++ tens 14 ++ ones 6)) false []) =
      some (junc 11 0 62, -57) := by
  simpa [root_low43_C0_to_junc11_max] using
    (runWithMax_toDelta 1347
      (z 2 (true::false::true::true::
        (ones 26 ++ tens 14 ++ ones 6)) false []))


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
    (runWithMax_toDelta 719 (junc 49 0 2))

#print axioms root_low43_C0_to_junc_max
#print axioms root_low43_C0_to_junc
#print axioms root_low43_junc23_to_junc11_max
#print axioms root_low43_C0_to_junc11_max
#print axioms root_low43_C0_to_junc11
#print axioms root_low_even_r96_max
#print axioms root_low_even_r96

end BB429Low43Continuation

import BB429JuncHeadExcursion
import Lean.Elab.Tactic.Omega

namespace BB429High2Prefix

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
  BB429FinishScanEDelta BB429JuncHeadExcursion

/-- The C/1 endpoint of the high-2 C/B sweep, in nearest-first zipper form.
    The left stack is (10)^(2u+2) followed by six ones; the right stack is
    11 01. -/
def high2SweepStart (u : Nat) : Zipper :=
  z 2 (tens (2*u+2) ++ ones 6) true (ones 2 ++ [false,true])

/-- Shifting the left head across the first one changes the nearest-first
    (10)^n 1^6 stack into (01)^n 1^5. -/
theorem tens_append_ones6 (n : Nat) :
    tens n ++ ones 6 = true :: (pairs01 n ++ ones 5) := by
  induction n with
  | zero => simp [tens, pairs01, ones]
  | succ n ih =>
      simp only [tens, pairs01, List.cons_append]
      rw [ih]

/-- The C/B sweep endpoint enters the exact even S_E source configuration
    after a fixed 21-step setup. The head moves left by one. -/
theorem high2_to_sourceScanE (u : Nat) :
    runWithDelta 21 (high2SweepStart u) =
      some (sourceScanE (2*u+2) (sourceSuffix 0), -1) := by
  simp only [high2SweepStart]
  rw [tens_append_ones6]
  rfl

/-- Compose the fixed setup, the proved even S_E-to-Junc macro, and the
    proved Junc(2,v,1)-to-MidA excursion. This gives an exact raw zipper
    predecessor for the high-2 J branch. -/
theorem high2_to_midA (u : Nat) :
    runWithDelta
      (21 + (crossTime (2*(u+1))+1 + (12+2*(2*(u+1))) +
        (2*(2*(u+1)+2)+6)))
      (high2SweepStart u) =
      some (midA2 (2*u+4) 1, 5) := by
  rw [BB429SourceE1Delta.runWithDelta_add, high2_to_sourceScanE]
  simp only [Option.bind_some]
  rw [BB429JuncHeadExcursion.sourceScanE_finishC_even_midA_delta]
  simp [Int.add_assoc]

#print axioms high2_to_sourceScanE
#print axioms high2_to_midA

end BB429High2Prefix

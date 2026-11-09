import Agent8DigitChargeSource

/-!
Full source-exact #623 return oracle using the two-input ternary digitCode
rather than recursive three-input drainB. This includes all original
branches, the nested evalA branch, successful states and source halts.
The equality is for the unmodified Cryptids highLevelNext itself.
It does not decide the unbounded blank-origin orbit.
-/
namespace BB6.Agent8NextDigitSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DigitChargeSource

def nextDigit : HighLevelState → Option HighLevelState
  | .D a d =>
    if a = 0 then
      if d % 2 = 1 then (digitCode (d+1) 2).map (realize 2 2)
      else some (.D d 7)
    else if d % 2 = 1 ∧ a ≥ d+5 then
      (digitCode (a-d-5) (d+3)).map (realize 5 (d+3))
    else if d % 2 = 0 ∧ a ≥ d+3 then
      (digitCode (a-d-2) (d+2)).map (realize 2 (d+2))
    else if a % 2 = 1 then none
    else if a = d+2 then (digitCode 0 a).map (realize 2 a)
    else if d % 2 = 1 then
      (digitCode (d+4-a) (a-1)).map (realize 3 (a-1))
    else (evalA (d+1-a) a (2*a+5)).bind (fun p =>
      (digitCode p.1 p.2.1).map (realize p.2.2 p.2.1))

/-- Exact equation between the new lossless transducer return map and
the actual machine's original accelerated high-level transition. -/
theorem nextDigit_exact (s : HighLevelState) :
    nextDigit s = highLevelNext s := by
  cases s with
  | D a d =>
    simp only [nextDigit,highLevelNext,drainB_digitCode]

/-- The two-input decoder accepts precisely the original complete returns. -/
theorem nextDigit_none_iff_source (s : HighLevelState) :
    nextDigit s = none ↔ highLevelNext s = none := by
  rw [nextDigit_exact]

#print axioms nextDigit_exact
#print axioms nextDigit_none_iff_source
end BB6.Agent8NextDigitSource

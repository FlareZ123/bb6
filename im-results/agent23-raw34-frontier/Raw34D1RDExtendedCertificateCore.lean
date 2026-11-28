import Raw34D1RDOneStepCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Soundness-preserving extension of the original-source sparse
Turing-machine witness checker: finite halting traces up to 59 source
steps plus arbitrary finite oriented side cycles, with a genuine
WeightedBound 64 on every total compatible machine. No custom
machine semantics, trust in the generator or native decision oracle. -/
namespace BB6.Agent23Raw34Extended
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent50SideCycle
open BB6.Agent23Raw34Next

def check64 (w : Witness) : Bool :=
  match w.cert with
  | .halt n => decide (n+1 ≤ 59) && finiteHaltCheck (table w.codes) n
  | .side entry period right boundary =>
      decide (0 < period) && fastSideCycleCheck (table w.codes)
        entry period right boundary

theorem check64_sound (w : Witness) (h : check64 w = true) :
    ∀ m, compatible (table w.codes) m → WeightedBound 64 m := by
  cases w with
  | mk codes cert =>
    cases cert with
    | halt n =>
      have hh : decide (n+1 ≤ 59) = true ∧
          finiteHaltCheck (table codes) n = true := by
        simpa only [check64, Bool.and_eq_true] using h
      intro m hm
      exact weighted_of_margin 64 m
        ((finiteHaltCheck_sound (table codes) n 59
          (of_decide_eq_true hh.1) hh.2).sound m hm)
        (by decide)
    | side entry period right boundary =>
      have hh : decide (0 < period) = true ∧
          fastSideCycleCheck (table codes) entry period right boundary = true := by
        simpa only [check64, Bool.and_eq_true] using h
      intro m hm
      exact weighted_of_never 64 m
        (fastSideCycleCheck_sound (table codes)
          entry period right boundary (of_decide_eq_true hh.1)
          hh.2 m hm)

#print axioms check64_sound
end BB6.Agent23Raw34Extended

import D1ZeroRD
import D1SixReduce
import D1EightReduce
import D1NineReduce
import D1LateD0Reduce
import D1RemainingD0Reduce
set_option maxHeartbeats 0
namespace BB6.Agent6D1SecondLevel
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent6D1ZeroRD

/-- Exact two-level interface for the D1=0RD normalized Raw139 cylinder.
    All immediately periodic children at both split levels are discharged;
    the nine hypotheses below are precisely the remaining grandchild families. -/
theorem cover (B : Nat) (hB : 14 ≤ B)
    (h2 : ∀ n ∈ BB6.Agent6D1TwoReduce.hard,
      Cover (WeightedBound B) (BB6.Agent6D1TwoReduce.sub (BB6.Agent6D1TwoReduce.move n)))
    (h6 : ∀ n ∈ BB6.Agent6D1SixReduce.hard,
      Cover (WeightedBound B) (BB6.Agent6D1SixReduce.sub (BB6.Agent6D1SixReduce.move n)))
    (h8 : ∀ n ∈ BB6.Agent6D1EightReduce.hard,
      Cover (WeightedBound B) (BB6.Agent6D1EightReduce.sub (BB6.Agent6D1EightReduce.move n)))
    (h9 : ∀ n ∈ BB6.Agent6D1NineReduce.hard,
      Cover (WeightedBound B) (BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move n)))
    (h10 : ∀ n ∈ BB6.Agent6D1TenReduce.hard,
      Cover (WeightedBound B) (BB6.Agent6D1TenReduce.sub (BB6.Agent6D1TenReduce.move n)))
    (h16 : ∀ n ∈ BB6.Agent6D1SixteenReduce.hard,
      Cover (WeightedBound B) (BB6.Agent6D1SixteenReduce.sub (BB6.Agent6D1SixteenReduce.move n)))
    (h17 : ∀ n ∈ BB6.Agent6D1SeventeenReduce.hard,
      Cover (WeightedBound B) (BB6.Agent6D1SeventeenReduce.sub (BB6.Agent6D1SeventeenReduce.move n)))
    (h18 : ∀ n ∈ BB6.Agent6D1EighteenReduce.hard,
      Cover (WeightedBound B) (BB6.Agent6D1EighteenReduce.sub (BB6.Agent6D1EighteenReduce.move n)))
    (h19 : ∀ n ∈ BB6.Agent6D1NineteenReduce.hard,
      Cover (WeightedBound B) (BB6.Agent6D1NineteenReduce.sub (BB6.Agent6D1NineteenReduce.move n))) :
    Cover (WeightedBound B) BB6.Agent6D1ZeroRD.p := by
  apply BB6.Agent6D1ZeroRD.cover B (by omega)
  intro n hn
  simp [BB6.Agent6D1ZeroRD.hard] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BB6.Agent6D1TwoReduce.cover B (by omega) h2
  · exact BB6.Agent6D1SixReduce.cover B (by omega) h6
  · exact BB6.Agent6D1EightReduce.cover B (by omega) h8
  · exact BB6.Agent6D1NineReduce.cover B (by omega) h9
  · exact BB6.Agent6D1TenReduce.cover B (by omega) h10
  · exact BB6.Agent6D1SixteenReduce.cover B (by omega) h16
  · exact BB6.Agent6D1SeventeenReduce.cover B (by omega) h17
  · exact BB6.Agent6D1EighteenReduce.cover B (by omega) h18
  · exact BB6.Agent6D1NineteenReduce.cover B (by omega) h19

#print axioms cover
end BB6.Agent6D1SecondLevel

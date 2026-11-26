import C9PairBridge
import SparseBlankDelay

namespace BB6.Agent13.C9Bridge
open BB6Coverage BB6.Agent13BlankDelay

def partialTable (short : Bool) : PartialMachine := fun s => some (table short s)

theorem compatible_table (short : Bool) (m : Machine)
    (hm : compatible (partialTable short) m) : m = table short := by
  funext s
  exact hm s _ rfl

theorem delays_zero (short : Bool) :
    delays (zeroNext (table short)) 0 = [0] := by
  cases short <;> decide

theorem weight (short : Bool) :
    WeightedBound 3142249368711030 (table short) := by
  intro k d hk hd
  have he := halting_time_unique (table short) k (time short) hk (exact_halt short)
  have hd0 : d = 0 := by
    rw [delays_zero] at hd
    simpa using hd
  subst k
  subst d
  cases short <;> decide
end BB6.Agent13.C9Bridge

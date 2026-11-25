import Raw110WordTrace
import Raw110WordSource

namespace BB6.Agent7Raw110Late
open BB6Coverage BB6.Agent13BlankDelay
open BB6Raw110Trace

theorem fast_cover (B : Nat) (hB : 6659487 ≤ B) :
    Cover (WeightedBound B) (table false) :=
  cover_of_trace false 6659486 B hB fast_trace

theorem slow_cover (B : Nat) (hB : 6766859 ≤ B) :
    Cover (WeightedBound B) (table true) :=
  cover_of_trace true 6766858 B hB slow_trace

#print axioms fast_cover
#print axioms slow_cover
end BB6.Agent7Raw110Late

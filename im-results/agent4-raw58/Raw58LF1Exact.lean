import Raw58LF1SharpUpper
import Raw58LF1SharpLower

namespace BB6.Agent4Raw58LF1
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

theorem exact_weight (B : Nat) :
    (∀ m, compatible parent m → WeightedBound B m) ↔ 3055746 ≤ B := by
  constructor
  · exact lower B
  · intro h m hm n d hn hd
    exact Nat.le_trans (bound m hm n d hn hd) h

#print axioms exact_weight
end BB6.Agent4Raw58LF1

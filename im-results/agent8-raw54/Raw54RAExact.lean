import Raw54RACut
import Raw54RAAttained
namespace BB6.Agent8Raw54.RA
open BB6Coverage BB6.Agent13BlankDelay
theorem exact_bound (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ 363 ≤ B := by
  constructor
  · exact lower_bound B
  · intro h m hm n d hn hd
    exact Nat.le_trans (cover m hm n d hn hd) h
#print axioms exact_bound
end BB6.Agent8Raw54.RA

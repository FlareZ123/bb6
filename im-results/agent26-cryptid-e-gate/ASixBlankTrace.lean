import ASix
import EBlankTrace

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- An original six-state raw-machine blank-tape trace of 166,999,736 steps. -/
theorem blank166999736 :
  run 166999736 blank = init (List.replicate 27657 true) := by
  have ht : 166999736 = 23503104 + (12*3454*3454 + 97*3454 + 202) := by decide
  rw [ht, run_add, blank23503104]
  simpa only [Nat.reduceMul, Nat.reduceAdd] using full_A_six 3454

#print axioms blank166999736
end CryptidBoundary

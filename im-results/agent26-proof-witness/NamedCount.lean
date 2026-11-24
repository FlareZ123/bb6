import Witness
import ReachRules
import ReachCount
open ReachRules

private def sweepWitness (n : Nat) (l r : List Bool) : ReachesStar move
    (config l (List.replicate n false ++ r)) (config (List.replicate n true ++ l) r) :=
  ⟨n, sweep_count n l r⟩

-- Eager named replacement prevents even attempting to unfold the huge sweep.
theorem huge_count (l r : List Bool) : ReachesIn move (2^2000)
    (config l (List.replicate (2^2000) false ++ r))
    (config (List.replicate (2^2000) true ++ l) r) :=
  witness_replaced% (sweep (2^2000) l r) using [] replacing [sweep := sweepWitness]

#print axioms huge_count

import Witness
import ReachRules
open ReachRules

recover_count ReachRules.triple as triple_exact positive
recover_count ReachRules.single as single_exact

theorem triple_count (l r : List Bool) : ReachesIn move 3
    (config l (false::true::false::r)) (config (true::true::true::l) r) :=
  (witness_proof% (triple l r) using []).2

theorem triple_rewrite_count (l r : List Bool) : ReachesIn move 3
    (config l (false::true::false::r)) (config (List.replicate 3 true ++ l) r) :=
  (witness_proof% (triple_rewrite l r) using []).2

theorem sweep_count (n : Nat) (l r : List Bool) : ReachesIn move n
    (config l (List.replicate n false ++ r)) (config (List.replicate n true ++ l) r) := by
  induction n generalizing l with
  | zero => exact witness_proof% (sweep 0 l r) using []
  | succ n ih =>
    let h (l' : List Bool) : ReachesStar move
        (config l' (List.replicate n false ++ r)) (config (List.replicate n true ++ l') r) := ⟨n, ih l'⟩
    have hr := witness_proof% (sweep (n+1) l r) using [h]
    simpa only [Nat.add_comm] using hr

#print axioms triple_exact
#print axioms single_exact
#print axioms triple_count
#print axioms triple_rewrite_count
#print axioms sweep_count

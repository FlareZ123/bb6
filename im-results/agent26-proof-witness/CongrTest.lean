import Witness
import ReachRules
open ReachRules

theorem rewritten (l l' r : List Bool) (hl : l = l') : ReachesPlus move
    (config l' (false::true::false::r)) (config (true::true::true::l) r) :=
  Eq.mp (congrFun' (congrArg (ReachesPlus move) (congrArg (fun x => config x (false::true::false::r)) hl)) _) (triple l r)

theorem rewrittenBoth (l l' r r' : List Bool) (hl : l = l') (hr : r = r') : ReachesPlus move
    (config l' (false::true::false::r)) (config (true::true::true::l) r') :=
  Eq.mp (congr (congrArg (ReachesPlus move) (congrArg (fun x => config x (false::true::false::r)) hl))
    (congrArg (config (true::true::true::l)) hr)) (triple l r)

theorem rewritten_exact (l l' r : List Bool) (hl : l = l') : ReachesIn move 3
    (config l' (false::true::false::r)) (config (true::true::true::l) r) :=
  (witness_proof% (rewritten l l' r hl) using []).2

theorem rewrittenBoth_exact (l l' r r' : List Bool) (hl : l = l') (hr : r = r') : ReachesIn move 3
    (config l' (false::true::false::r)) (config (true::true::true::l) r') :=
  (witness_proof% (rewrittenBoth l l' r r' hl hr) using []).2

#print axioms rewritten_exact
#print axioms rewrittenBoth_exact

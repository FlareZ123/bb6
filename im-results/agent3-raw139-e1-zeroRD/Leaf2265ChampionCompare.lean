import Leaf2265Bridge
import ChampionPow1024

namespace BB6.Agent3Leaf2265ChampionCompare

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6Coverage.Agent48DirectRoot

/-!
The decisive local threshold bridge, conditional only on the exact source
macro trace and champion second-increment modules compiling successfully.
The literal one-hole cylinder is not a whole Raw139 parent and does not
decrease the current global Canonical39 remainder by itself.
-/

abbrev attainedScore : Nat := proposedTM63Moves + 7

theorem leaf_bound_below_champion :
    BB6.Agent3Leaf2265Bridge.n + 6 ≤ attainedScore := by
  calc
    BB6.Agent3Leaf2265Bridge.n + 6 ≤ 2^1024 := by decide
    _ ≤ proposedTM63Moves + 7 :=
      BB6.Agent3ChampionPow1024.champion_score_ge_pow1024

theorem one_hole_cover_at_champion :
    Cover (WeightedBound attainedScore) BB6.Agent3Leaf2265Bridge.ctr := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent3Leaf2265Bridge.weighted.sound m hm k d hk hd)
    leaf_bound_below_champion

#print axioms leaf_bound_below_champion
#print axioms one_hole_cover_at_champion

end BB6.Agent3Leaf2265ChampionCompare

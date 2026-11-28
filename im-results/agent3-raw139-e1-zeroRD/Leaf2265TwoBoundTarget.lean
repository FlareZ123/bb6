import Leaf2265Bridge
import TwoBoundAudit
import ChampionPow1024

set_option maxRecDepth 1000000

namespace BB6.Agent3Raw139D0OneLFTarget
open BB6Coverage
open BB6.Agent13BlankDelay

/-!
A common quantitative target for the 4,873 ordinary local leaves and
the two astronomically late exceptional leaves of Raw139 E1=0RD D0=1LF.
This is a *conditional integration interface*, not a parent cover.
-/

def finiteBound : Nat := 148142
def largeBound : Nat := 2^32768

theorem finite_le_large : finiteBound ≤ largeBound := by
  calc
    finiteBound ≤ 2^18 := by decide
    _ ≤ largeBound :=
      Nat.pow_le_pow_right (by decide) (by decide)

theorem leaf2265_bound_le_large :
    BB6.Agent3Leaf2265Bridge.n + 6 ≤ largeBound := by
  calc
    BB6.Agent3Leaf2265Bridge.n + 6 ≤ 2^1024 := by decide
    _ ≤ largeBound :=
      Nat.pow_le_pow_right (by decide) (by decide)

theorem leaf2265_cover_at_large :
    Cover (WeightedBound largeBound) BB6.Agent3Leaf2265Bridge.ctr := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent3Leaf2265Bridge.weighted.sound m hm k d hk hd)
    leaf2265_bound_le_large

theorem large_le_attained_champion :
    largeBound ≤ BB6ChampionArithmetic.proposedTM63Moves + 7 := by
  exact BB6.Agent3ChampionPow1024.champion_score_ge_pow_of_le
    32768 (by decide)

/-- A fully source-proved TwoBoundAudit at finiteBound/largeBound would
    transport to an ordinary Cover at the *attained* champion score. -/
theorem lift_hybrid_cover (p : PartialMachine)
    (h : Cover (WeightedBound largeBound) p) :
    Cover (WeightedBound
      (BB6ChampionArithmetic.proposedTM63Moves + 7)) p := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (h.sound m hm k d hk hd)
    large_le_attained_champion

#print axioms finite_le_large
#print axioms leaf2265_bound_le_large
#print axioms leaf2265_cover_at_large
#print axioms large_le_attained_champion
#print axioms lift_hybrid_cover
end BB6.Agent3Raw139D0OneLFTarget

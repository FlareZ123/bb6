import TM63CompleteIncrementSource
import Rst1PrimeBridge6Source
import S1CountedDrain

namespace BB6Coverage.Agent48DirectRoot
open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent8Rst1PrimeTail
open BB6ChampionArithmetic

/-- The exact marker-1 zero-counter reset, including the source drain. -/
theorem reset_source : ResetSource := by
  intro L a b h
  have hp := rst1Prime_counted_macro L a b h
  have hb : 2^b-1 < 2^b := Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
  have hr := s1Config_reset_prefix_then_counted_drain
    (L+a+2) (2^(L+a+2)-2^a-1) 2 b b (h+5+3*(b:Int))
    (s1Config L 0 1 a 0 b h) (97+12*(L+a)+3*b) hp hb
  have hc : resetCost L a b = (97+12*(L+a)+3*b)+drainCost (2^b-1) 0 := by
    unfold resetCost
    have hd := drainCost_binary_additive b
    omega
  rw [hc,resetIndex_eq_pow_sub]
  exact hr

/-- The full proposed TM63 score is attained by the original machine. -/
theorem champion_attained_exact : Attainable (proposedTM63Moves+7) :=
  direct_root_attainment increment_source reset_source

#print axioms reset_source
#print axioms champion_attained_exact
end BB6Coverage.Agent48DirectRoot

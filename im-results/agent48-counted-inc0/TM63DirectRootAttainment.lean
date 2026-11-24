import TM63CompleteIncrementSource
import Rst1PrimeBridge6Source
import S1CountedDrain
import TerminalEncoderBridge

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

/-- Named literal-table witness, with the final halting query excluded. -/
theorem champion_halts_exact : HaltsAfter championTable (proposedTM63Moves+6) :=
  direct_root_halts increment_source reset_source

/-- The only remaining mathematical premise for exact BB(6) in this model
is the universal upper-bound certificate at the now-attained score. -/
theorem champion_maximum_of_cover
    (cert : Cover (DecidedBelow (proposedTM63Moves+7)) emptyTable) :
    Attainable (proposedTM63Moves+7) ∧
    ∀ score, Attainable score → score ≤ proposedTM63Moves+7 :=
  ⟨champion_attained_exact, maximal_runtime_if_cover _ cert⟩

#print axioms champion_halts_exact
#print axioms champion_maximum_of_cover
#print axioms reset_source
#print axioms champion_attained_exact
end BB6Coverage.Agent48DirectRoot

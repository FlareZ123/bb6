import M0EvenEightValuationQ4Source
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Marker-0, n=8q all-valuation counted increment

This final wrapper applies the established S1 counted drain to the
valuation-dependent q4 reset-prefix theorem.
-/

namespace BB6Coverage.Agent48M0EvenEightValuationCountedSource

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent48M0EvenEightValuationQ4Source
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

/-- Complete original-source counted increment for marker 0 and n=8q,
for every q>0 (all 2-adic valuations). -/
theorem m0EvenEight_valuation_counted_increment_source
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hq : 0 < q)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 0 (8*q) a b)
      (s1Config L (8*q) 0 a 0 b h) =
      some (s1Config L (8*q-1) 2 (a+b+1) 0 (2^b-1)
        (h+5+(3*b:Int))) := by
  have hprefix := m0EvenEight_valuation_q4_reset_prefix_source
    L q a b h hL hq hbound ha
  have hdrain : 2^b-1 < 2^(a+b+1) := by
    have h := resetDrainBound a b 0 ha
    simpa [resetDelta] using h
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*q-1) 2 (a+b+1) b (h+5+(3*b:Int))
    (s1Config L (8*q) 0 a 0 b h)
    (resetPrefixCost 0 (8*q) a b) hprefix hdrain
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms m0EvenEight_valuation_counted_increment_source

end BB6Coverage.Agent48M0EvenEightValuationCountedSource

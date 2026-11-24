import M2EvenSixGenericSource
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Counted completion of the generic m=2, n=8*q+6 source row

The generic q4 source module proves the exact reset prefix for every
admissible quotient q. This adapter composes the already-proved S1
counted drain, so the result is a complete original-TM2 increment rather
than only a prefix ending with an all-ones counter.
-/

namespace BB6Coverage.Agent44M2EvenSixGenericCounted

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6ChampionArithmetic
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent44M2EvenSixGenericSource

set_option autoImplicit false

/-- Complete source-level m=2 increment for every n=8*q+6, including
the exact all-ones S1 drain. -/
theorem m2EvenSix_generic_counted_increment_source
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+6 < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 2 (8*q+6) a b)
      (s1Config L (8*q+6) 2 a 0 b h) =
      some (s1Config L (8*q+5) 1 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m2EvenSix_generic_q4_reset_prefix_source
    L q a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 2 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*q+5) 1 (a+b+2) b (h+5+3*b)
    (s1Config L (8*q+6) 2 a 0 b h)
    (resetPrefixCost 2 (8*q+6) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms m2EvenSix_generic_counted_increment_source

end BB6Coverage.Agent44M2EvenSixGenericCounted

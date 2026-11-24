import M2EvenResidueSix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Counted completion of the m=2, n=16*k+6 source reset

The residue-six q4 module proves the exact reset prefix.  This adapter
attaches the already-generic S1 counted drain, giving the complete
original-table increment needed by the TM63 root countdown.
-/

namespace BB6Coverage.Agent42M2EvenResidueSixCounted

open BB6ChampionArithmetic
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent48M2EvenResidueSix

/-- Complete source-level m=2 increment for every admissible n=16*k+6,
including the exact all-ones S1 drain. -/
theorem m2Even_residue6_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*k+6 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 2 (16*k+6) a b)
      (s1Config L (16*k+6) 2 a 0 b h) =
      some (s1Config L (16*k+5) 1 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m2Even_residue6_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 2 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (16*k+5) 1 (a+b+2) b (h+5+3*b)
    (s1Config L (16*k+6) 2 a 0 b h)
    (resetPrefixCost 2 (16*k+6) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms m2Even_residue6_counted_increment_source

end BB6Coverage.Agent42M2EvenResidueSixCounted

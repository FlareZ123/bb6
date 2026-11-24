import M0OddResidueSeven
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Counted-drain completion of the m=0,n=16*r+7 reset prefix

This module deliberately separates the quantified q4 reset-prefix proof
from the reusable all-positive S1 counted-drain dependency.  Its transitive
axiom audit must independently reject sorryAx; the reset-prefix theorem in
M0OddResidueSeven.lean does not depend on this module.
-/

namespace BB6Coverage.Agent41M0OddResidueSevenCounted

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6ChampionArithmetic
open BB6Coverage.Agent41M0OddResidueSeven
open BB6Coverage.Agent48CountedInc0

/-- Complete original-TM2 m=0 increment for every admissible n=16*r+7,
including the exact geometric all-ones drain. -/
theorem m0Odd_residue7_counted_increment_source
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 0 (16*r+7) a b)
      (s1Config L (16*r+7) 0 a 0 b h) =
      some (s1Config L (16*r+6) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m0Odd_residue7_q4_reset_prefix_source
    L r a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 0 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (16*r+6) 2 (a+b+1) b (h+5+3*b)
    (s1Config L (16*r+7) 0 a 0 b h)
    (resetPrefixCost 0 (16*r+7) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms m0Odd_residue7_counted_increment_source

end BB6Coverage.Agent41M0OddResidueSevenCounted

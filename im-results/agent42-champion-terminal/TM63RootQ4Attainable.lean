import TM63RootQ4Drain
import S1ChampionCountedReset
import Lean.Elab.Tactic.Omega

/-!
# Root-connected TM63 attained-score interface

This is the single attained-score composition for the current blank-root
q4/drain prefix and the existing terminal counted-reset adapter.  The only
missing machine-specific input is the exact original-source continuation
from the q4/drain endpoint to the final m=1,n=1 reset input, together with
that final reset-prefix run.  No such continuation is asserted here.
-/

namespace BB6Coverage.Agent42RootAttainable

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42TerminalJoin
open BB6ChampionArithmetic

/--
If the original TM63 table continues from the root-connected q4/drain
endpoint to the final S1 state with marker 1 and index 0, and the final
(1,1) reset prefix reaches the terminal S0 pre-drain state, then the
terminal adapter proves an attained Busy Beaver lower bound at the exact
composed primitive-step count.

The first premise is precisely the still-missing middle of the published
Coq itinerary; the second is the final Rst0/Rst1/Rst2 source prefix.  This
theorem does not assume that either premise has been proved.
-/
theorem tm2_attainable_after_root_q4_drain_to_terminal_reset
    (suffixSteps L a b : Nat) (h : Int)
    (ha : 0 < a)
    (hstage :
      run tm2 suffixSteps
        (s1Config 3 6 1 71 0 (2^63-1) 223) =
        some (s1Config L 0 1 a 0 b h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 a b)
        (s1Config L 0 1 a 0 b h) =
        some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
          (a+b+resetDelta 1) (2^b-1) 0 h)) :
    Attainable
      (rootQ4DrainMoves + suffixSteps +
        proposedIncrementCost 1 1 a b +
        terminalMoves L (a+b+resetDelta 1) + 7) := by
  have hblank :
      run tm2 (rootQ4DrainMoves + suffixSteps) blank =
        some (s1Config L 0 1 a 0 b h) := by
    rw [run_add tm2 blank rootQ4DrainMoves suffixSteps]
    rw [tm2_blank_reaches_q4_drain_endpoint]
    exact hstage
  exact champion_attainable_after_s1_countedRst012_m1n1
    (s1Config L 0 1 a 0 b h)
    (rootQ4DrainMoves + suffixSteps) L a b h ha hblank
    (by simpa [s1Config] using hfinal)

/-- The root component already has a closed exact cost, independent of the
unknown middle itinerary. -/
theorem rootQ4Drain_attained_prefix_length :
    rootQ4DrainMoves = 6*4^63 + 42*2^63 + 27487 :=
  rootQ4DrainMoves_closed

#print axioms tm2_attainable_after_root_q4_drain_to_terminal_reset
#print axioms rootQ4Drain_attained_prefix_length

end BB6Coverage.Agent42RootAttainable

import S1CountedInc0
import TerminalEncoderBridge
import Lean.Elab.Tactic.Omega

/-!
# S1-specialized champion counted-reset composition

The terminal bridge's fixed S0 left context is exactly the S1 encoder
instance `s1Config L 0 0`.  The parity-complete S1 decrement theorem
therefore discharges the bridge's remaining uniform Inc0 premise for this
champion context, leaving only the genuine blank-root and reset-prefix
witnesses.
-/

namespace BB6Coverage.Agent48CountedInc0

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42ChampionTerminal

/-- Replace the terminal bridge's universal arbitrary-context Inc0
assumption by the parity-complete S1 theorem at its actual champion context.
The only machine-specific hypotheses left are the blank-root witness and
the reset-prefix witness. -/
theorem champion_attainable_after_s1_countedRst012
    (cfg : Config) (rootSteps L a b m n : Nat) (h : Int)
    (ha : 0 < a)
    (hblank : run tm2 rootSteps blank = some cfg)
    (hprefix :
      run tm2 (resetPrefixCost m n a b) cfg =
        some (s1Config L 0 0 (a+b+resetDelta m) (2^b-1) 0 h)) :
    Attainable
      (rootSteps + proposedIncrementCost m n a b +
        terminalMoves L (a+b+resetDelta m) + 7) := by
  let l : List Bool := markerWord 0 ++ d0 ++ binDec L 0 ++ lh
  have hprefix' :
      run tm2 (resetPrefixCost m n a b) cfg =
        some (s0Config l (a+b+resetDelta m) (2^b-1) 0 h) := by
    simpa [l,s1Config] using hprefix
  have hInc0 :
      ∀ z c, 0 < z → z < 2^(a+b+resetDelta m) →
        run tm2 (inc0Cost z c)
          (s0Config l (a+b+resetDelta m) z c h) =
          some (s0Config l (a+b+resetDelta m) (z-1) (c+1) h) := by
    intro z c hz hzlt
    obtain ⟨q,r,len,hfactor,ha',hq,hrun⟩ :=
      s1Config_counted_decrement L 0 0 (a+b+resetDelta m) z c h hz hzlt
    have hv := v2_of_odd_factorization z q r hfactor
    simpa [inc0Cost,l,s1Config,hv] using hrun
  have hprefix'' :
      run tm2 (resetPrefixCost m n a b) cfg =
        some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
          (a+b+resetDelta m) (2^b-1) 0 h) := by
    simpa [l] using hprefix'
  exact champion_attainable_after_countedRst012
    cfg rootSteps L a b m n h ha hblank hprefix'' hInc0

/-- The prefix parameter choice in Agent 42's intended reset theorem is
`m=1,n=1`: `nextMarker 1=0` and `1-1=0`, so its output left context
is exactly the terminal bridge's fixed `s1Config L 0 0` context. -/
theorem champion_attainable_after_s1_countedRst012_m1n1
    (cfg : Config) (rootSteps L a b : Nat) (h : Int)
    (ha : 0 < a)
    (hblank : run tm2 rootSteps blank = some cfg)
    (hprefix :
      run tm2 (resetPrefixCost 1 1 a b) cfg =
        some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
          (a+b+resetDelta 1) (2^b-1) 0 h)) :
    Attainable
      (rootSteps + proposedIncrementCost 1 1 a b +
        terminalMoves L (a+b+resetDelta 1) + 7) := by
  apply champion_attainable_after_s1_countedRst012
    cfg rootSteps L a b 1 1 h ha hblank
  simpa [s1Config] using hprefix

#print axioms champion_attainable_after_s1_countedRst012
#print axioms champion_attainable_after_s1_countedRst012_m1n1

end BB6Coverage.Agent48CountedInc0

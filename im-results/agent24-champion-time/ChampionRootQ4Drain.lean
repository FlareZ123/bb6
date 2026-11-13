import TM63RootQ4Drain
import ChampionRootBridge

/-!
# Actual champion root transport to the counted q4-drain endpoint

The counted q4/drain theorem is stated for the BusyCoq TM63 table.  The
published champion table is the state-renamed TM1 table, whose blank root
is transported to TM63's state-E root by the six-step source bridge.
This file lifts the exact full-tape endpoint through that transport.
It proves a finite prefix of the actual champion; it does not assert that
the endpoint halts or that the BB(6) upper bound is known.
-/

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent8S1Encoder

/-- Inverse of the published champion-to-TM63 state permutation. -/
def championPermInv : StatePerm where
  forward := championPerm.backward
  backward := championPerm.forward
  leftInverse := championPerm.rightInverse
  rightInverse := championPerm.leftInverse

/-- Exact length of the actual champion's transported root prefix. -/
def championRootQ4DrainMoves : Nat := rootQ4DrainMoves + 6

theorem championRootQ4DrainMoves_closed :
    championRootQ4DrainMoves = 6*4^63 + 42*2^63 + 27493 := by
  unfold championRootQ4DrainMoves
  rw [rootQ4DrainMoves_closed]
  omega

/-- Run-level form of the six-step blank-root transport.  The full tape,
head, and state are transported, not merely the halting predicate. -/
theorem champion_run_offset (n : Nat) :
    run championTable (15+n) blank =
      (run tm2 (9+n) blank).map (renameConfig championPermInv) := by
  have hrename := rename_run championPerm championTable
    (blankAt (0 : Fin 6)) (15+n)
  have hrename' :
      run tm2 (15+n) (blankAt (4 : Fin 6)) =
        (run championTable (15+n) blank).map (renameConfig championPerm) := by
    simpa only [champion_renamed, championPermA, rename_blankAt,
      blankAtZero] using hrename
  have hjoin := all_join n
  have hrel :
      run tm2 (9+n) blank =
        (run championTable (15+n) blank).map (renameConfig championPerm) :=
    hjoin.symm.trans hrename'
  have hmap := congrArg
    (fun o : Option Config => o.map (renameConfig championPermInv)) hrel
  have hcomp :
      (renameConfig championPermInv ∘ renameConfig championPerm) = id := by
    funext c
    cases c
    simp [renameConfig, championPermInv, championPerm.leftInverse]
  simpa [Option.map_map, hcomp] using hmap.symm

/-- The actual champion blank root reaches the same full tape as the
TM63 q4/drain endpoint, with the champion's correctly renamed state, after
exactly six more primitive transitions. -/
theorem champion_blank_reaches_q4_drain_endpoint :
    run championTable championRootQ4DrainMoves blank =
      some (renameConfig championPermInv
        (s1Config 3 6 1 71 0 (2^63-1) 223)) := by
  have hbound : 9 ≤ rootQ4DrainMoves := by
    rw [rootQ4DrainMoves_closed]
    omega
  have h9 : 9+(rootQ4DrainMoves-9)=rootQ4DrainMoves := by omega
  have h15 : 15+(rootQ4DrainMoves-9)=rootQ4DrainMoves+6 := by omega
  have h := champion_run_offset (rootQ4DrainMoves-9)
  rw [h15,h9,tm2_blank_reaches_q4_drain_endpoint] at h
  simpa [championRootQ4DrainMoves] using h

#print axioms champion_run_offset
#print axioms championRootQ4DrainMoves_closed
#print axioms champion_blank_reaches_q4_drain_endpoint

end BB6Coverage.Agent24ChampionTime

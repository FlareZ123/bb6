import TerminalChampion
import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
# Counted terminal-prefix join for the six-state champion

The terminal S1 macro is already source-certified for arbitrary exterior
tape. This file composes that result with an arbitrary genuine TM63 blank
prefix and the independently proved six-step TM63/champion root offset.
The resulting Attainable theorem has the correct final-query convention.
It deliberately leaves the difficult prefix proof as an explicit premise.
-/

namespace BB6Coverage.Agent42TerminalJoin

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.TerminalBridge

/-- Successful primitive moves in the source-certified terminal S1 macro. -/
def terminalMoves (L a : Nat) : Nat := 59 + 12*(L+a)

/-- Any genuine blank-root TM63 prefix that reaches a tape in the terminal
S1 section halts after the exact prefix-plus-terminal number of successful
moves. The tape exterior is unrestricted. -/
theorem tm2_halts_after_terminal_prefix
    (n L a : Nat) (t : Int → Bool) (h : Int)
    (hprefix : run tm2 n blank = some ⟨3,h,t⟩)
    (hsection : TerminalFinish.SectionBits L a t h) :
    HaltsAfter tm2 (n + terminalMoves L a) := by
  obtain ⟨c, hterminal, hquery⟩ :=
    tm2_terminal_query_any_tape L a t h hsection
  have hlive : run tm2 (n + terminalMoves L a) blank = some c := by
    rw [show n + terminalMoves L a = n + (59+12*(L+a)) by rfl]
    rw [run_append, hprefix]
    simpa [terminalMoves] using hterminal
  have hhalt : run tm2 (n + terminalMoves L a + 1) blank = none := by
    have hsum : n + terminalMoves L a + 1 =
        n + (59+12*(L+a)+1) := by
      unfold terminalMoves
      omega
    rw [hsum, run_append, hprefix]
    simpa [terminalMoves] using hquery
  change (run tm2 (n + terminalMoves L a) blank).isSome = true ∧
    run tm2 (n + terminalMoves L a + 1) blank = none
  exact ⟨by simp [hlive], hhalt⟩


/-- Generic halting-time bridge: any proved TM63 blank-root halting
time N is transported to the published champion's root, six successful
moves earlier. The lower bound N≥9 follows from tm2_min_halt. -/
theorem champion_halts_after_tm2_haltsAfter
    (N : Nat) (h : HaltsAfter tm2 N) :
    HaltsAfter championTable (N+6) := by
  have hN : 9 ≤ N := tm2_min_halt N h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hN
  have htm2 : HaltsAfter tm2 (9+k) := by
    simpa [hk] using h
  have hchamp := (champion_halts_offset k).mpr htm2
  have hscore : 15+k = N+6 := by omega
  simpa [hscore] using hchamp

/-- Minimal attainable-score adapter for any original-source TM63
blank-root halting theorem. The final undefined query contributes the
seventh move relative to the TM63 successful-move count. -/
theorem champion_attainable_of_tm2_haltsAfter
    (N : Nat) (h : HaltsAfter tm2 N) :
    Attainable (N+7) := by
  refine ⟨championTable, N+6,
    champion_halts_after_tm2_haltsAfter N h, ?_⟩
  rfl

/-- Root-corrected champion halting theorem for a terminal S1 prefix. -/
theorem champion_halts_after_terminal_prefix
    (n L a : Nat) (t : Int → Bool) (h : Int)
    (hprefix : run tm2 n blank = some ⟨3,h,t⟩)
    (hsection : TerminalFinish.SectionBits L a t h) :
    HaltsAfter championTable (n + terminalMoves L a + 6) := by
  exact champion_halts_after_tm2_haltsAfter
    (n + terminalMoves L a)
    (tm2_halts_after_terminal_prefix n L a t h hprefix hsection)

/-- Direct attainable-score interface for downstream counted-prefix proofs.
No root offset or final halt-query arithmetic remains to be reconstructed. -/
theorem champion_attainable_after_terminal_prefix
    (n L a : Nat) (t : Int → Bool) (h : Int)
    (hprefix : run tm2 n blank = some ⟨3,h,t⟩)
    (hsection : TerminalFinish.SectionBits L a t h) :
    Attainable (n + terminalMoves L a + 7) := by
  exact champion_attainable_of_tm2_haltsAfter
    (n + terminalMoves L a)
    (tm2_halts_after_terminal_prefix n L a t h hprefix hsection)

#print axioms tm2_halts_after_terminal_prefix
#print axioms champion_halts_after_terminal_prefix
#print axioms champion_attainable_after_terminal_prefix

end BB6Coverage.Agent42TerminalJoin

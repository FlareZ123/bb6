#!/usr/bin/env python3
"""Apply an isolated Lean theorem patch to the pinned Cryptids source tree."""
from pathlib import Path
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: patch_hphase_growth.py <upstream-module.lean>")

target = Path(sys.argv[1])
source = target.read_text()
marker = "end BusyBeaver.M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA"
if marker not in source:
    raise SystemExit("expected namespace terminator not found")
if "hphase_growth_76_raw" in source:
    raise SystemExit("patch already applied")

patch = r'''
/-! ## Agent 48: tail-parametric H-phase growth macro -/

private def hPhaseP : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (1, 0), (0, 0), (19, 0)]

private def hPhaseB : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (0, 0), (2, 0), (0, 0), (0, 0),
   (0, 0), (2, 0), (0, 0), (0, 0), (0, 0), (16, 0)]

/-- The 76-successor H-phase growth macro, checked as 254 raw TM steps.
The arbitrary suffix is preserved and one block B is inserted before it. -/
theorem hphase_growth_76_raw (T : List (ℕ × ℕ)) :
    (evalStackCfg .CR_n_n [(1, 0), (0, 0)] (hPhaseP ++ hPhaseB ++ T)) [target]⊢⁺
      evalStackCfg .CR_n_n [(1, 0), (0, 0)] (hPhaseP ++ hPhaseB ++ hPhaseB ++ T) := by
  dsimp only [evalStackCfg, cfg_CR_n_n]
  simp only [encLeft, encRight, Nat.mod_one]
  execute 254

'''
target.write_text(source.replace(marker, patch + marker))
print("patched", target)

#!/usr/bin/env python3
"""Unverified patch: append the root-connected DR/G/B 254-raw-step theorem to #490."""

from pathlib import Path
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: patch_root_growth.py <upstream-490-module.lean>")

target = Path(sys.argv[1])
source = target.read_text()
marker = "end BusyBeaver.M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH"
if marker not in source:
    raise SystemExit("expected #490 namespace terminator not found")
if "root_growth_76_raw" in source:
    raise SystemExit("patch already applied")

patch = r'''
/-! ## Agent 48: root-connected DR/G/B 76-step insertion -/

private def rootGrowthG : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (1, 0), (0, 0), (1, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (1, 0)]

private def rootGrowthB : List (ℕ × ℕ) :=
  [(16, 0), (0, 0), (0, 0), (0, 0), (2, 0), (0, 0),
   (0, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0)]

/-- The root-reachable DR/G/B insertion macro is 254 raw TM steps.
The arbitrary suffix T is preserved while one block B is inserted. -/
private theorem root_growth_76_raw (T : List (ℕ × ℕ)) :
    (closedStackSystem.evalStackCfg .DR_n_n rootGrowthG
      ((1, 0) :: rootGrowthB ++ T)) [target]⊢⁺
    (closedStackSystem.evalStackCfg .DR_n_n rootGrowthG
      ((1, 0) :: rootGrowthB ++ rootGrowthB ++ T)) := by
  dsimp [closedStackSystem, ClosedStackSystem.evalStackCfg, rootGrowthG, rootGrowthB]
  execute 254

#print axioms root_growth_76_raw

'''
target.write_text(source.replace(marker, patch + marker))
print("patched", target)

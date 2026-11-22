#!/usr/bin/env python3
"""Unverified patch: append the 526-step H(7) entry and 254-step H-phase growth theorems to #85."""

from pathlib import Path
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: patch_hphase_entry_growth.py <upstream-85-module.lean>")

target = Path(sys.argv[1])
source = target.read_text()
marker = "end BusyBeaver.M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA"
if marker not in source:
    raise SystemExit("expected #85 namespace terminator not found")
if "hphase_entry_157_raw" in source:
    raise SystemExit("patch already applied")

patch = r'''
/-! ## Agent 48: standalone H-phase entry and growth raw-step theorems -/

private def hPhaseP : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (1, 0), (0, 0), (19, 0)]

private def hPhaseB : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (0, 0), (2, 0), (0, 0), (0, 0),
   (0, 0), (2, 0), (0, 0), (0, 0), (0, 0), (16, 0)]

private def hPhaseU : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (0, 0), (12, 0), (0, 0), (0, 0),
   (0, 0), (12, 0), (0, 0), (0, 0), (0, 0), (12, 0),
   (0, 0), (0, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0), (0, 0)]

private def hPhaseH7L : List (ℕ × ℕ) :=
  [(0, 0), (1, 0), (0, 0), (1, 0), (0, 0), (1, 0), (0, 0),
   (1, 0), (0, 0), (1, 0), (0, 0), (1, 0), (0, 0), (1, 0),
   (0, 0), (1, 0), (0, 0), (0, 0), (0, 0), (1, 0), (0, 0),
   (0, 0), (0, 0)]

private def hPhaseH7R : List (ℕ × ℕ) :=
  [(2, 0), (0, 0), (0, 0), (0, 0), (0, 0)]

/-- H(7) reaches C1 in 157 outer successors / 526 raw TM steps. -/
private theorem hphase_entry_157_raw :
    (closedStackSystem.evalStackCfg .CR_n_n hPhaseH7L hPhaseH7R) [target]⊢⁺
    (closedStackSystem.evalStackCfg .CR_n_n ([(1, 0), (0, 0)])
      (hPhaseP ++ hPhaseB ++ hPhaseU)) := by
  dsimp [closedStackSystem, ClosedStackSystem.evalStackCfg, cfg_CR_n_n,
    hPhaseH7R, hPhaseH7L, hPhaseP, hPhaseB, hPhaseU]
  simp only [encLeft, encRight, Nat.mod_one]
  execute 526

/-- The 76-successor H-phase growth macro is 254 raw TM steps and preserves
an arbitrary finite suffix T while inserting one block B. -/
private theorem hphase_growth_76_raw (T : List (ℕ × ℕ)) :
    (closedStackSystem.evalStackCfg .CR_n_n [(1, 0), (0, 0)]
      (hPhaseP ++ hPhaseB ++ T)) [target]⊢⁺
    (closedStackSystem.evalStackCfg .CR_n_n [(1, 0), (0, 0)]
      (hPhaseP ++ hPhaseB ++ hPhaseB ++ T)) := by
  dsimp [closedStackSystem, ClosedStackSystem.evalStackCfg, cfg_CR_n_n,
    hPhaseP, hPhaseB]
  simp only [encLeft, encRight, Nat.mod_one]
  execute 254

#print axioms hphase_entry_157_raw
#print axioms hphase_growth_76_raw

'''
target.write_text(source.replace(marker, patch + marker))
print("patched", target)

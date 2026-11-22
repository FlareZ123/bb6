/-- Fixed left block inserted by the corrected #490 mirrored-root replay. -/
private def rootMirroredBlock : List (ℕ × ℕ) :=
  [(0, 0), (2, 0), (0, 0), (0, 0), (0, 0), (2, 0),
   (0, 0), (0, 0), (0, 0), (16, 0), (0, 0), (0, 0)]

/-- Fixed right stack at the phase-aligned mirrored-root growth state. -/
private def rootMirroredRight : List (ℕ × ℕ) :=
  [(0, 0), (1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (1, 0), (0, 0), (0, 0), (0, 0)]

/-- The corrected #490 blank-root replay has a DR state whose 76-successor
    macro preserves the right stack and inserts one copy of rootMirroredBlock
    immediately after the leading left digit. The proof expands exactly 254
    primitive transitions in the pinned #490 machine module. -/
theorem root_mirrored_growth_76_raw (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (closedStackSystem.evalStackCfg StackMode.DR_n_n
        ((1, 0) :: rootMirroredBlock ++ T) rootMirroredRight)
      (closedStackSystem.evalStackCfg StackMode.DR_n_n
        ((1, 0) :: rootMirroredBlock ++ rootMirroredBlock ++ T) rootMirroredRight) := by
  dsimp [closedStackSystem, ClosedStackSystem.evalStackCfg, rootMirroredBlock, rootMirroredRight]
  execute 254

#print axioms root_mirrored_growth_76_raw

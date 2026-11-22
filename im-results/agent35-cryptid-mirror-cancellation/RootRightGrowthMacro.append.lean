set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

/-- Ten-entry left stack at the blank-root-connected DR/G/B family. -/
def rootRightGrowthLeft : List (ℕ × ℕ) :=
  [(0,0),(0,0),(1,0),(0,0),(1,0),(0,0),(0,0),(0,0),(0,0),(1,0)]

/-- Twelve-entry block inserted on the right by each 76-successor macro. -/
def rootRightGrowthBlock : List (ℕ × ℕ) :=
  [(16,0),(0,0),(0,0),(0,0),(2,0),(0,0),
   (0,0),(0,0),(2,0),(0,0),(0,0),(0,0)]

/-- Exact-source, arbitrary-suffix 76-step growth identity on the
    blank-root-connected (no-extra-swap) DR/G/B family. -/
theorem root_right_growth_76_raw (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (closedStackSystem.evalStackCfg StackMode.DR_n_n
        rootRightGrowthLeft (((1,0) :: rootRightGrowthBlock) ++ T))
      (closedStackSystem.evalStackCfg StackMode.DR_n_n
        rootRightGrowthLeft
          (((1,0) :: rootRightGrowthBlock) ++ (rootRightGrowthBlock ++ T))) := by
  change ReachesPlus target
    (mirrorCfg f
      (M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.closedStackSystem.evalStackCfg
        StackMode.DR_n_n (((1,0) :: rootRightGrowthBlock) ++ T) rootRightGrowthLeft))
    (mirrorCfg f
      (M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.closedStackSystem.evalStackCfg
        StackMode.DR_n_n
          (((1,0) :: rootRightGrowthBlock) ++ (rootRightGrowthBlock ++ T))
          rootRightGrowthLeft))
  execute 254

#print axioms root_right_growth_76_raw

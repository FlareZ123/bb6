set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-- Fixed 12-entry left block inserted by the corrected #490 mirrored-root replay. -/
def rootMirroredBlock : List (ℕ × ℕ) :=
  [(0, 0), (2, 0), (0, 0), (0, 0), (0, 0), (2, 0),
   (0, 0), (0, 0), (0, 0), (16, 0), (0, 0), (0, 0)]

/-- Fixed right stack at the root-growth invariant. -/
def rootMirroredRight : List (ℕ × ℕ) :=
  [(0, 0), (1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (1, 0), (0, 0), (0, 0), (0, 0)]

/-- Tail of the first root-reachable pumping seed; its length is 18. -/
def rootMirroredSeedTail : List (ℕ × ℕ) :=
  [(0, 0), (12, 0), (0, 0), (0, 0), (0, 0), (12, 0),
   (0, 0), (0, 0), (0, 0), (12, 0), (0, 0), (0, 0),
   (0, 0), (2, 0), (0, 0), (0, 0), (0, 0), (0, 0)]

def rootMirroredSeedLeft : List (ℕ × ℕ) :=
  ((1, 0) :: rootMirroredBlock) ++ rootMirroredSeedTail


/-- Concrete stack encodings for the mirrored wrapper. These are the
    configuration-level equations used by the source execution proofs. -/
theorem root_evalStackCfg_DR (L R : List (ℕ × ℕ)) :
    closedStackSystem.evalStackCfg StackMode.DR_n_n L R =
      Cfg.headLeft A
        (M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.closedStackSystem.encRight L)
        (M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.closedStackSystem.encLeft R) := by
  rfl

theorem root_evalStackCfg_CR (L R : List (ℕ × ℕ)) :
    closedStackSystem.evalStackCfg StackMode.CR_n_n L R =
      Cfg.headLeft C
        (M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.closedStackSystem.encRight R)
        (M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.closedStackSystem.encLeft L) := by
  rfl

/-- The first token closure from the 7-step root-entry state costs 29 raw
    transitions and lands in this mirrored CR stack configuration. -/
theorem root_mirrored_token_closure :
    ReachesPlus target
      (closedStackSystem.evalStackCfg StackMode.DR_n_n [(0, 0), (0, 0)] [(1, 0)])
      (closedStackSystem.evalStackCfg StackMode.CR_n_n
        [(1, 0)] [(0, 0), (0, 0), (0, 0), (1, 0)]) := by
  rw [root_evalStackCfg_DR, root_evalStackCfg_CR]
  execute 29

/-- The next 259 ordinary outer successors cost 848 raw transitions and reach
    the first phase-aligned DR pumping seed. -/
theorem root_mirrored_ordinary_prefix :
    ReachesPlus target
      (closedStackSystem.evalStackCfg StackMode.CR_n_n
        [(1, 0)] [(0, 0), (0, 0), (0, 0), (1, 0)])
      (closedStackSystem.evalStackCfg StackMode.DR_n_n
        rootMirroredSeedLeft rootMirroredRight) := by
  rw [root_evalStackCfg_CR, root_evalStackCfg_DR]
  execute 848

theorem root_mirrored_seed_from_stack :
    ReachesPlus target
      (closedStackSystem.evalStackCfg StackMode.DR_n_n [(0, 0), (0, 0)] [(1, 0)])
      (closedStackSystem.evalStackCfg StackMode.DR_n_n
        rootMirroredSeedLeft rootMirroredRight) :=
  ReachesPlus.trans root_mirrored_token_closure root_mirrored_ordinary_prefix

/-- The blank-root run reaches the first pumping seed in 884 raw transitions:
    7 initial transitions, 29 token-closure transitions, then 848 ordinary. -/
theorem init_reaches_root_mirrored_seed :
    ReachesPlus target (init [])
      (closedStackSystem.evalStackCfg StackMode.DR_n_n
        rootMirroredSeedLeft rootMirroredRight) := by
  have h0 : ReachesPlus target (init [])
      (closedStackSystem.evalStackCfg StackMode.DR_n_n [(0, 0), (0, 0)] [(1, 0)]) := by
    have htarget :
        closedStackSystem.evalStackCfg StackMode.DR_n_n [(0, 0), (0, 0)] [(1, 0)] =
          ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default)
            <{{A}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default) := by
      rfl
    rw [htarget]
    execute 7
  exact ReachesPlus.trans h0 root_mirrored_seed_from_stack

/-- The 76-successor macro preserves the right stack and arbitrary suffix,
    inserting one further copy of rootMirroredBlock after the leading 1.
    The source proof expands exactly 254 primitive transitions. -/
theorem root_mirrored_growth_76_raw (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (closedStackSystem.evalStackCfg StackMode.DR_n_n
        (((1, 0) :: rootMirroredBlock) ++ T) rootMirroredRight)
      (closedStackSystem.evalStackCfg StackMode.DR_n_n
        (((1, 0) :: rootMirroredBlock) ++ (rootMirroredBlock ++ T)) rootMirroredRight) := by
  rw [root_evalStackCfg_DR]
  execute 254

/-- The invariant set consists of all DR configurations with the fixed leading
    block and fixed right stack. The macro maps every member back into this set,
    so the blank-root machine never halts. -/
theorem root_mirrored_isNotHalt : IsNotHalt target := by
  let P : Cfg (Fin 2) (Fin 6) → Prop := fun c =>
    ∃ T : List (ℕ × ℕ),
      c = closedStackSystem.evalStackCfg StackMode.DR_n_n
        (((1, 0) :: rootMirroredBlock) ++ T) rootMirroredRight
  refine IsNotHalt.of_reachesPlus_invariant
    (P := P)
    (c₀ := closedStackSystem.evalStackCfg StackMode.DR_n_n
      rootMirroredSeedLeft rootMirroredRight) ?_ ?_ ?_
  · exact ReachesPlus.to_star init_reaches_root_mirrored_seed
  · exact ⟨rootMirroredSeedTail, rfl⟩
  · intro c hc
    rcases hc with ⟨T, rfl⟩
    refine ⟨closedStackSystem.evalStackCfg StackMode.DR_n_n
        (((1, 0) :: rootMirroredBlock) ++ (rootMirroredBlock ++ T)) rootMirroredRight,
      root_mirrored_growth_76_raw T, ?_⟩
    exact ⟨rootMirroredBlock ++ T, rfl⟩

#print axioms root_mirrored_token_closure
#print axioms root_mirrored_ordinary_prefix
#print axioms init_reaches_root_mirrored_seed
#print axioms root_mirrored_growth_76_raw
#print axioms root_mirrored_isNotHalt

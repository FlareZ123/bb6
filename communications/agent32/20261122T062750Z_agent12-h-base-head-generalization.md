# Agent 12 correction: H-base macro generalizes to any head a≥2

The m/Q-block statement in my earlier handoff is a corollary of a stronger, simpler source-transcribed identity. For every numeric head a≥2 and arbitrary finite suffix T:

```text
S^179(H(7; [a] ++ T))
  = DR(G, [1] ++ B ++ [16,0,0,0] ++ Q^3 ++ [a] ++ T).
```

Here [a] denotes the pair-stack head [(a,0)]; the suffix T is a list of pairs. The current V8 tests use second-coordinate-zero numeric tails and an opaque sentinel; arbitrary nonzero second coordinates remain for the Lean source proof.

Proposed Lean shape:

```lean
theorem h_base_raw (a : Nat) (ha : 2 ≤ a) (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (closedStackSystem.evalStackCfg .CR_n_n (hLeft 7) ((a, 0) :: T))
      (closedStackSystem.evalStackCfg .DR_n_n gLeft
        ([(1, 0)] ++ bWord ++ [(16, 0), (0, 0), (0, 0), (0, 0)] ++
         qWord ++ qWord ++ qWord ++ ((a, 0) :: T))) := by
  -- Depending on the local execute simplifier, split on a=2 versus a≥3.
  execute 591
```

The raw branch histogram is unchanged for a=2,3,4,5,12,100,100000 and suffixes empty, numeric, and opaque. It totals 179 outer successors / 591 raw steps, with no token-normalizer calls. This is stronger than the earlier m formulation: for the root input Q^966 ++ Hright, take a=12 and T equal to the remaining suffix; the output is exactly Q^3 ++ Q^966 ++ Hright = Q^969 ++ Hright after the fixed prefix.

I updated RootCountdownGrowth.md, ModeDRBranchAudit.md, RootCorridorMacro.md, and the regression harness to use this stronger form. The older m-based statement remains a useful corollary but is no longer the preferred theorem target.
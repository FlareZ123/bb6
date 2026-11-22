# Agent 12 correction: exact pair encoding for the DR/G/B theorem

Correction to my immediately preceding theorem draft: its two `(0,2)` entries were placeholders and are **wrong**. Use `(2,0)` at both 2-valued positions. Here is the clean statement with the correct pair encoding and no placeholders:

```lean
theorem drgb_growth_raw (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (closedStackSystem.evalStackCfg .DR_n_n
        [(0, 0), (0, 0), (1, 0), (0, 0), (1, 0),
         (0, 0), (0, 0), (0, 0), (0, 0), (1, 0)]
        ([(1, 0), (16, 0), (0, 0), (0, 0), (0, 0), (2, 0),
          (0, 0), (0, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0)] ++ T))
      (closedStackSystem.evalStackCfg .DR_n_n
        [(0, 0), (0, 0), (1, 0), (0, 0), (1, 0),
         (0, 0), (0, 0), (0, 0), (0, 0), (1, 0)]
        ([(1, 0), (16, 0), (0, 0), (0, 0), (0, 0), (2, 0),
          (0, 0), (0, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0)] ++
         [(16, 0), (0, 0), (0, 0), (0, 0), (2, 0), (0, 0),
          (0, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0)] ++ T)) := by
  change ReachesPlus target
    ((encRight [(0, 0), (0, 0), (1, 0), (0, 0), (1, 0),
      (0, 0), (0, 0), (0, 0), (0, 0), (1, 0)]) <{{A}}
      (encLeft ([(1, 0), (16, 0), (0, 0), (0, 0), (0, 0), (2, 0),
        (0, 0), (0, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0)] ++ T)))
    ((encRight [(0, 0), (0, 0), (1, 0), (0, 0), (1, 0),
      (0, 0), (0, 0), (0, 0), (0, 0), (1, 0)]) <{{A}}
      (encLeft ([(1, 0), (16, 0), (0, 0), (0, 0), (0, 0), (2, 0),
        (0, 0), (0, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0)] ++
        [(16, 0), (0, 0), (0, 0), (0, 0), (2, 0), (0, 0),
         (0, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0)] ++ T)))
  execute 254
```

The source mapping to state `A` is grounded by the wrapper's own `init_reaches_nontrivial` theorem at lines 107–115, whose `htarget` reduces the root `.DR_n_n` configuration to a tape in state `A`. The pair lists above encode the exact numeric words G and B from RootCountdownGrowth.md.

Please use this corrected snippet instead of the placeholder-bearing prior message. I have not committed it as an uncompiled theorem.

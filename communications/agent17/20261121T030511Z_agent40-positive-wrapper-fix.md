# Agent 40: correction to positive-offset wrapper snippet

One small Lean direction error in my immediately preceding snippet: `reach_last_edge` needs `10 ≠ y), while the parameter is `hnot : y ≠ 10`. Replace the line by either

```lean
  obtain ⟨x,hreach,hedge⟩ :=
    SheepEvenReachInverse.reach_last_edge hy (Ne.symm hnot)
```

or `(by omega)`. The remaining wrapper statement and source conversion are unchanged.

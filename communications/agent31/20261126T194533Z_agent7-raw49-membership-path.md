# Agent 7 follow-up: exact path expression for Raw49 membership

I identified the canonical path expression for the Raw49 parent, using your existing `BB6.Agent31StableParentBatch` imports:

```lean
abbrev p49 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨true,true,2⟩)
```

This follows the first three entries (B0=1RC, C0=0RD, D0=1LD) and takes the sibling D1=1RC rather than the path's D1=1RE. Its table is exactly `1RB---_1RC---_0RD---_1LD1RC_------_------`. Please use this alias for `p49_count64` and `p49_count59` in the existing membership preflight if convenient. I will not duplicate the Canonical59 assembly path.

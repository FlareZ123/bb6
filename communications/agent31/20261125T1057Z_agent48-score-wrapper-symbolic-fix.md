# Agent 48 follow-up: avoid reducing the giant champion score

One additional diagnosis from the 45577606094 log: both wrapper files still declare `abbrev championScore := proposedTM63Moves + 7`. The `Nat.pow` kernel-evaluation failures at the wrapper theorem declarations are consistent with this reducible alias forcing evaluation of the enormous score. Consider changing it to an opaque-enough `def championScore : Nat := proposedTM63Moves + 7`, and keep the lower-bound proof symbolic rather than rewriting the giant score into a numeral:

```lean
have hroot : 27959 ≤ threeSectionMoves 27959 3 7 6 63 + 7 :=
  rootSteps_le_score 27959 3 7 6 63
have hscore : 7014 < threeSectionMoves 27959 3 7 6 63 + 7 := by omega
simpa only [championScore, ← threeSectionMoves_root] using hscore
```

In `champion_not_weighted_7014`, also bind the theorem result explicitly:
```lean
have hB : 7014 < proposedTM63Moves + 7 := by
  simpa only [championScore] using champion_score_gt_7014
```
before the final `omega`. The current `MixedBound109Composition` still has `by decide [championTable]` at line 30; replace it with `by decide` if this obsolete wrapper remains in the dependency closure.

I have not edited either Agent31 file. This is a suggested minimal repair; the decisive test is one source-closure compile, not another scan.
— Agent 48

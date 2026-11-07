# Agent 40: stronger #623 mass-growth lemma

I locally kernel-checked a stronger drain bound using verbatim copies of the pinned upstream `evalA`, `drainB`, and `highLevelNext` equations.

For every successful drain:
```
drainB a b d = some (.D aa dd)
```
the proved bound is
```
a + d + 3*b + (if b = 0 then 0 else 1) <= aa + dd.
```

The key evaluator lemma is
```
evalA a k m = some (aa,bb,dd)
  -> a + m + k <= aa + 3*bb + dd + 1.
```
It follows by induction on `a`. Strong induction on the drain index `b`, with the source input `k=b-1` and third counter `d+2*b+3`, then gives the drain bound.

Case analysis over the actual high-level branch table yields:
```
a % 2 = 0
0 < d
highLevelNext (.D a d) = some (.D aa dd)
  -> a + d + min a d + 5 <= aa + dd.
```
This strengthens `next_strict_mass`'s universal additive +7 bound on the even-first-counter positive-second-counter domain. The branch margins from the drain lemma are: far-left odd +5 over the target, far-left even +2, diagonal +2, near-odd exact, and near-even exact via the evaluator lemma. The zero axis is immediate from its two branches.

Verification status: the proof compiles locally with Lean 4.36.0-rc2 against copied source equations. It is **not yet source-import certified** against the actual upstream definitions. I have not changed your files or workflow. The natural next step is to put the two lemmas and the high-level corollary in a separate import-only module, then add a selective step to the existing pinned manual source workflow if you agree.

This is a growth theorem for the accelerated system, not a blank-root halting/nonhalting decision. It may sharpen mass-scale terminal-gate arguments.

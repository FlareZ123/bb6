# Agent 42: bound premise in direct composition

One detail to include in the previous direct-composition note: `source_weighted_local bound` takes the arithmetic premise
```coq
(N.to_nat 1000000 + 6 <= bound)%nat
```
before its `forall x` local classifier property. Thus instantiate `actual_source_coverage` with `Hlocal := source_weighted_local bound HB`, where `HB` is proved once for the proposed global bound (e.g. `N.to_nat proposedTM63Moves + 7`). The rest of the composition is unchanged.

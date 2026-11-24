# Agent 42: exact Hlocal adapter for actual_source_coverage

A small type-shape detail in the direct composition: `source_weighted_local bound HB x` takes `source_good x` *before* its classifier match, whereas `actual_source_coverage` wants `source_good x` (inside `source_weighted_safe x`) after the branch's child-safety premise. The adapter can be written explicitly:

```coq
assert (Hlocal :
  forall x,
    match decider (tm x) with
    | Halt h =>
        Forall (source_weighted_safe bound) (expand' x h) ->
        source_weighted_safe bound x
    | NonHalt => source_weighted_safe bound x
    | Unknown => True
    end).
{
  intro x.
  destruct (decider (tm x)) eqn:Hd; simpl.
  - intros Hchildren Hgood.
    pose proof (source_weighted_local bound HB x Hgood) as Hloc.
    rewrite Hd in Hloc.
    exact (Hloc Hchildren).
  - intros Hgood.
    pose proof (source_weighted_local bound HB x Hgood) as Hloc.
    rewrite Hd in Hloc.
    exact Hloc.
  - exact I.
}
```

This is just the premise-order adapter; it does not add any mathematical assumption beyond `HB`. Then `actual_source_coverage` can be applied with this `Hlocal` and the 129 holdout premise.

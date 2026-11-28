# Raw11 exact 299→148 residual theorem after Extra132 and Extra140

## Result

The Raw11 route now has an exact source-accepted conditional reduction from its
299 original open cylinders to **148 residual Cover hypotheses** at every common
weighted bound `B ≥ 4663`.

The accepted chain is:
- q0-root53 and Extra28 reduce 299→150;
- Extra132 has a complete source-accepted
  `Cover (WeightedBound 691)` for table code `27874661676483464`;
- Extra140 has a complete source-accepted
  `Cover (WeightedBound 491)` for table code `27872991061794760`;
- `BB6.Agent44Raw11Extra132140After150.raw11_cover_from_148` removes exactly
  those two literal parents from the accepted 150-entry complement.

The consumer kernel-proves that both literal parents are members of the
150-entry predecessor and that
`(prior.length, remaining.length) = (150,148)`.  Removal is by exact
`sameTable` equality, so no sibling cylinder is silently discarded.

## Source acceptance

GitHub Actions run
[46164340074](https://github.com/FlareZ123/bb6/actions/runs/46164340074)
completed successfully on Lean 4.36.0-rc2 from main commit
`138a874bc06b825ebe78859d9ad64530ead4a2a1`.

The exact source
`im-results/agent44-raw11-extra28/Raw11Extra132140After150.lean` was compiled
against the independently accepted predecessor, Extra132 and Extra140 proof
objects.  The audit rejects `sorryAx` and `native_decide`.  The final theorem

`BB6.Agent44Raw11Extra132140After150.raw11_cover_from_148`

depends only on `[propext, Classical.choice, Quot.sound]`; the exact census,
membership, and both lifted parent Covers have the same standard profile
(except the literal-code equality, which needs only `propext`).

Artifact **15271268459**,
`agent44-raw11-exact-299-to-148-extra132-extra140`, has ZIP SHA-256
`9f341f8db7d6c09181db414bf203fa3fb47eafbbaf4c8c50d9e9f57b587dc9f7`.

## Scope

This is a rigorous reduction of one current Raw11 conditional interface.  It
does not discharge the remaining 148 cylinders and therefore is not a
universal BB(6) upper bound.  The accepted global maximality interface remains
a separate Canonical frontier until Raw11 and the other retained Covers are
fully discharged and consumed there.

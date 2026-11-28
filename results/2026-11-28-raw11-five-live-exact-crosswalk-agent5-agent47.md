# Raw11 exact five-live crosswalk: 150→145 conditional residuals

**Status:** original-source Lean 4.36.0-rc2 accepted, 28 November 2026. This is an exact roster theorem and conditional Raw11 reduction. It does **not** claim that all five named parents are already covered.

Starting from the accepted exact **299→150** Raw11 complement
`BB6.Agent47Raw11Extra28After151.remaining`, the source module
`Raw11FiveLiveAfter150.lean` identifies five exact live parents:

- Extra132,
- Extra140,
- q0-148,
- q0-150,
- q0-151.

Their packed table codes are kernel-decided as

```text
27874661676483464
27872991061794760
27168822759015208
27168823376846760
27168823685762536
```

The theorem `all_members_in_150` proves that every one of these five literal partial machines occurs in the accepted 150-entry complement through exact `sameTable` witnesses. The theorem `exact_census` then proves that removing exactly these literals changes the residual roster from **150 to 145**.

The exported conditional theorem is

```lean
BB6.Agent47Raw11FiveLiveAfter150.raw11_cover_from_145
```

For any common weighted threshold `B ≥ 4663`, Covers of those five parents plus Covers of the exact 145-entry complement imply a Cover of the original Raw11 parent. Thus each future accepted Cover among these five has a formally authenticated route into the current Raw11 lineage.

## Source acceptance

CI **46161798762** succeeded after repairing the workflow's dependency staging for the already-accepted Extra28 predecessor. Artifact **15270018439** has SHA-256
`0a1a191e9b4de570c2852dea19f115e3198e99ae353777531649f229cb171949`.
The source SHA-256 is
`298708c60647eefb7a04f7bd7c66cb24b5b4bd0984a5fc73d2e1faa48ba7a416`.

The audited theorem profiles are:

- `literal_codes`: `[propext]`;
- `all_members_in_150`: `[propext, Classical.choice, Quot.sound]`;
- `exact_census`: `[propext, Classical.choice, Quot.sound]`;
- `raw11_cover_from_145`: `[propext, Classical.choice, Quot.sound]`.

No `sorryAx` or `native_decide` occurs in the accepted log.

This exact crosswalk is especially useful for q0-151: its previously open one-hole source cylinder is now universally nonhalting, and its authenticated frozen parent is being assembled separately at weighted bound 59,642. Once that parent Cover is accepted, the q0-151 hypothesis in this five-parent theorem can be discharged by an exact source successor.

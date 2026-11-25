# A source-accepted two-parent reduction to 76 canonical residuals

**Status (25 November 2026): proved conditional reduction; BB(6) remains unresolved.**

## The theorem

Let `root` be the standard first-one normalized six-state root and let
`roster76 = BB6.Agent47CanonicalTwoParent.roster76`. The accepted Lean
development proves

```lean
theorem roster76_sound :
  ∀ m, compatible root m →
    WeightedBound 7014 m ∨
      ∃ e ∈ roster76, TNFQuotientCompatible e.2 m
```

and `roster76.length = 76`.

Consequently, for every `B ≥ 7014`, if every retained representative has a
`Cover (WeightedBound B)` and a blank-start machine attains `B), then
`ExactBB6 B`. The target theorem is
`BB6.Agent31CanonicalTwoParentRosterOnly.exact_at_target`.

This is a quotient-level reduction, not a completed upper bound: all 76
residual Covers remain explicit premises. The champion witness is a separate
attainment premise, supplied by the exact primitive-step champion result. No
physical completion-mass reduction is claimed.

## Exact parent cuts

The starting source-accepted canonical quotient roster has 78
representatives. Two exact five-move residual parents are removed in sequence:

| Parent | Exact partial table | Accepted bound | Resulting roster |
|---|---|---:|---:|
| raw107 (`p107`) | `1RB---_1RC---_0RD---_1LD1RE_---0RB_------` | 815 | 77 |
| raw114 (`p114`) | `1RB---_1RC---_0RD---_1LD1RE_---0LD_------` | 7014 | 76 |

The Lean definitions are in
[`CanonicalTwoParentGraft.lean`](../im-results/agent47-rooted-tnf/CanonicalTwoParentGraft.lean).
They establish `roster107.length = 77` and `roster76.length = 76`, with
`roster76_sound` proved by two applications of the exact `graftRoster`
refinement theorem.

The concrete wrapper is
[`CanonicalTwoParentRosterOnly.lean`](../im-results/agent31-shared-core/CanonicalTwoParentRosterOnly.lean):

- `p107_matches_raw107` is definitional equality between the canonical
  residual and the original raw107 parent.
- `p107_bound` instantiates the source-accepted
  `Raw107ParentClosure.all_completions` at 815.
- `p114_bound` instantiates the source-accepted
  `CanonicalRaw114Accepted.parent_bound` at 7014.
- `roster76_sound` combines both bounds and preserves every retained
  quotient-compatible residual.
- `exact_at_target` leaves all 76 Covers and the attaining witness explicit.

The lower raw107 threshold is lifted monotonically to 7014; no stronger
machine-specific claim is inferred.

## Source audit

The combined wrapper passed the **exactness job** (job
139320746934) of GitHub Actions run
[45647053824](https://github.com/FlareZ123/bb6/actions/runs/45647053824)
at source revision `6df83f9e433d7e8c75e074b1789a457be6f4a4f3`.
The job compiled the Raw107 parent closure against the accepted canonical
core, then compiled the concrete two-parent wrapper. Its manifest reports:

- theorem: `BB6.Agent31CanonicalTwoParentRosterOnly.exact_at_target`;
- residual count: **76**;
- weighted cutoff: **7014**;
- precompiled core modules reused: **51**;
- the accepted `CanonicalRaw114Accepted.olean` hash was unchanged by reuse;
- every named theorem profile contained only
  `propext`, `Classical.choice`, and `Quot.sound`;
- the workflow's forbidden-`sorryAx`/`native_decide` guard passed.

The raw107 parent proof was independently accepted in
[run 45533196624](https://github.com/FlareZ123/bb6/actions/runs/45533196624)
at bound 815. The raw114 source wrapper was accepted in
[run 45554648116](https://github.com/FlareZ123/bb6/actions/runs/45554648116)
at bound 7014, using the source-accepted raw114 parent proof.

**Artifact-label warning:** the combined run uploaded artifact
[15043876968](https://github.com/FlareZ123/bb6/actions/runs/45647053824/artifacts/15043876968)
under the name
`canonical73-raw110-raw112-roster-consumer-certified`. That label is
misleading: its embedded manifest identifies the theorem as the two-parent
`CanonicalTwoParentRosterOnly.exact_at_target` and records 76 residuals,
not 73. The separate reusable raw107 shared-core artifact is
[15043282896](https://github.com/FlareZ123/bb6/actions/runs/45647053824/artifacts/15043282896).
The overall workflow run concluded failure because a downstream canonical72
consumer job failed; the exactness job itself succeeded and uploaded both
artifacts. Do not treat the downstream failure as invalidating the successful
exactness job, and do not use the mislabeled artifact name as evidence for a
73-residual theorem.

## Remaining mathematical work

The 76 residual representatives still require universal Covers at the
champion score (or a stronger suitable bound), and the champion must be
instantiated as the attaining witness. The result does not establish
`BB(6) ≤ B` unconditionally and does not determine `BB(6)`.

A separate follow-on source audit is attempting to combine additional
raw117, raw112, raw110 and raw121 parent cuts. Until its own source and axiom
audit succeeds, those proposed 73-/72-residual counts are not accepted here.

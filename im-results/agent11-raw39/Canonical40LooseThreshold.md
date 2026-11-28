# Canonical40 at any higher score: removing parents without a 6,766,859 local cutoff

**Status (28 November 2026):** theorem candidate [`Raw39Canonical40LooseThreshold.lean`](Raw39Canonical40LooseThreshold.lean), original-source audit [CI 46113771109](https://github.com/FlareZ123/bb6/actions/runs/46113771109) underway. Do **not** report this generalization as source-accepted before the CI gate succeeds. The two ingredients separately used below are source-accepted: [Canonical40 quotient](../agent31-shared-core/) and generic [`removeParents_sound`](../agent31-shared-core/Canonical68StableBatch.lean).

## The mathematical observation

The accepted Canonical40 soundness states, with
`C=6,766,859`, root `root`, and its exact accepted representative roster `R`:

```text
For every normalized six-state machine M:
 compatible root M →
 WeightedBound C M ∨ ∃ e∈R, TNFQuotientCompatible e M.
```

For **any** natural number `B≥C`, the same theorem remains true replacing
`WeightedBound C` by `WeightedBound B`. This is immediate by monotonicity
on the first disjunct, without modifying any quotient representative or
looking at any machine again.

Now take **any finite list of selected parent partial tables** `P`,
each satisfying the accepted first-one root/action condition and a source
certificate `Cover (WeightedBound B) p` at **this new B**. The already accepted
polymorphic `removeParents_sound` theorem gives:

```text
∀ M compatible root,
  WeightedBound B M ∨
  ∃ e ∈ (R with every parent P removed),
    TNFQuotientCompatible e M.
```

If every remaining quotient representative is covered at `B`, and
`B` is the actual halting score of the champion witness, the accepted
`exact_from_quotient_roster` theorem derives `ExactBB6 B`.
Thus we are **not obliged** to establish a selected parent's exact
uniform bound below the old 6,766,859 cutoff; **a bound at the champion
score itself suffices.** This permits source-accepted parent results with
bounds larger than the historical intermediate cutoff, provided they do
not exceed the champion's attained score.

The Lean candidate supplies source statements:

- `sound40_at B hFloor`: widen original accepted Canonical40 disjunction.
- `remove_many_at B hFloor hRoots hParents`: generic finite parent batch at new threshold B.
- `exact_at_target B hFloor hSix hParent hLeaves champ`: target-score maximality.
- `exact_at_champion`: specialization to the accepted six-state champion.

All quantifiers are universal over total compatible completions; this is
not an empirical search or speculative numeric estimate.

## Why the old cutoff can make a correct parent proof impossible

This is not merely an optimization. The accepted [Raw13 one-hole exact-halting certificate](../../results/2026-11-28-raw13-hierarchical-carry-exact-halt-agent46.md) attains **44,423,003,584,937,617,011,264,491,061 primitive steps**. Its total halting completion extends the Raw13 cylinder whose three leading source transitions are `A0=1RB, B0=1RC, C0=1LA`; that cylinder also appears in the reconstructed Canonical40 raw-index audit (the latter's global identity remains a separate theorem obligation). The witness is already far larger than the historical cutoff **6,766,859**. Therefore a `Cover (WeightedBound 6766859)` of that *whole Raw13 parent* would be mathematically false: it would incorrectly exclude this witnessed halter. The champion score is vastly larger still.

A second decisive example is **Raw139**, which contains the exact [six-state champion halting machine](../../results/2026-11-24-champion-exact-attainment.md) in the project's present classification. The reconstructed Canonical40 list retains Raw139; the champion's exact symbolic score exceeds 6,766,859 by an immense margin. Therefore no proof can give a sound `Cover (WeightedBound 6766859) Raw139` either. Since eventual global exactness requires covering the champion-containing representative *at its attained score*, a target-score quotient-removal interface is mathematically essential, not merely a convenience. Literal roster membership and source-compatible import obligations still belong to the final global proof.

The parametric target-score approach avoids this false local precondition: a valid parent Cover at the actual champion score can coexist with known long halters while still supporting the exact global upper-bound argument. It does **not** automatically prove any such parent Cover. This distinction matters especially for parent classes that contain an explicit long-running halting completion. The finite roster proof should not accidentally make a local cutoff into a universal upper-bound obligation.

## Raw39 application

Raw39 P has a [source-accepted dominance theorem](../../results/2026-11-28-raw39-dominant-child-equivalence-agent11.md):

```text
∀ B≥15125, Bound B (A1=1LE child) →
  Cover (WeightedBound B) Raw39.
```

The champion's attained score `S = proposedTM63Moves+7` is already
provably above 6,766,859, hence above 15,125. Therefore, if one eventually
proves merely `Bound S (A1=1LE child)` (not necessarily the sharp
`Bound 28311`), the entire Raw39 parent can be removed at score S,
leaving only the other 39 Canonical40 Covers as separate obligations.

The proposed combined theorem is
`BB6.Agent11Raw39SoleObligation.exact_at_champion_if_oneLE_at_champion`,
pending a combined original-source Lean dependency merge in
[the Raw39 global consumer](consume_raw39_after_canonical40.py). Separately
accepted source theorem [46111496271](https://github.com/FlareZ123/bb6/actions/runs/46111496271)
covers the earlier **39+Raw39 Cover** quotient split at C; it does not
by itself establish this higher-threshold generalization.

**Limitation:** Neither local `Bound S (1LE)` nor the other 39 Covers is
proved by this transport. A count of 39 non-Raw39 representatives is only
conditional, and the full value of `BB(6)` remains open.

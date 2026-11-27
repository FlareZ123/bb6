# Raw47: consume a completed seven-hole parent on the accepted Canonical40 frontier

## Mathematical goal and current acceptance boundary

The source-accepted global quotient theorem
`BB6.Agent31Canonical40Extra57.exact_at_champion_score` reduces universal six-state, two-symbol blank-start maximality to weighted Covers of **40** specific residual representatives. This theorem was accepted in [run 46075158700](https://github.com/FlareZ123/bb6/actions/runs/46075158700) by consuming the independent Raw57 parent proof on the accepted Canonical41 predecessor. **It is conditional**: none of the 40 remaining Cover hypotheses may be silently discarded.

One retained representative is expected to be the seven-hole partial table

```
P47 = 1RB---_1RC---_0RD---_1LD0RC_------_------
```

The separate original-source Lean proof `BB6.Agent50Raw47Complete.cover_at` from [run 46068688341](https://github.com/FlareZ123/bb6/actions/runs/46068688341) establishes
`Cover (WeightedBound B) P47` for every `B ≥ 143977`. Its exact weighted threshold, with a 143975-live-step attaining witness and halt-query/delay surcharge, is established independently in [the Raw47 theorem report](../../results/2026-11-27-raw47-exact-weighted-maximum-agent50.md). This is **complete coverage of the Raw47 cylinder**, not a statement about the other 39 representatives.

The target Lean successor is `BB6.Agent50Canonical39Raw47.exact_at_champion_score` with the following meaning:

> **If** each of the 39 remaining exact quotient representatives has a `Cover (WeightedBound (proposedTM63Moves+7))`, **then** the exact certified champion score is the six-state Busy Beaver step maximum.

The new `roster39` is formed by the repository's source `removeParents` operation from the accepted `roster40` and the exact Raw47 parent. The new proof must certify the single matching roster element, the 39-count complement, removal soundness and the fixed-score conditional theorem. Reducing the hypothesis count is a genuine conditional-global proof advance **only after** original-source Lean compiles the successor.

## Reproduction and evidence

The preparatory driver `consume_after_canonical40.py` strictly checks the two accepted producer artifacts and their source versions, Lean 4.36.0-rc2 object hashes, exact prior-delta chain, all reused kernel imports and the theorem's transitive axiom profiles. It imports the accepted Canonical40 `Canonical40Extra57.olean`, proves the new Raw47 membership by finite `sameTable` comparison, transports `Raw47Complete.cover_at` to the common threshold 6,766,859, and constructs the 39-entry conditional consumer by reusing the same source `removeParents_sound` / `exact_from_quotient_roster` interface as Canonical40.

The current acceptance target is **manual** `.github/workflows/agent50-raw47-lifted.yml`, `mode=canonical39`, `raw47_run=46068688341`. The run [46083879711](https://github.com/FlareZ123/bb6/actions/runs/46083879711) is the first source attempt after a concrete namespace repair; **it is not assumed successful while in progress**. No `results/` claim or root-board decrement is justified before its final proof and axiom audit pass.

The earlier direct Canonical41 consumer `consume.py` is a superseded experimental branch, not the accepted global baseline. Its first run 46069652144 stopped at duplicate object extraction before Lean membership; run 46071815209 reached Lean but used unqualified `sameTable`, producing a compiler error. The exact definition is `BB6.Agent31FourHoleRoster.sameTable` in `FourHoleResidualRoster.lean`; both consumer preflights now explicitly open that namespace. Their failed job artifacts do **not** constitute theorem acceptance.

## Unresolved quantifier and next decisive action

Even if the Canonical39 theorem passes, universal maximality still requires `Cover` for **every** surviving representative. The hard arithmetic and symbolic-root machines remain undecided. At a failed source run, repair the *first actual* compiler/import collision and rerun only changed source. At a successful source run, publish the exact theorem, run ID, retained count, canonical delta digest and axiom profile as a new conditional reduction in `results/`; reconcile the global board and results map. Never count Raw57 or another already-consumed parent twice.

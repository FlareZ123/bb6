# Accepted Raw124 Canonical57 delta and remaining Raw59 edge

**Established conditional interface:** the exact Raw124 removal from the actual accepted Canonical58 roster passed in [run 45926694578](https://github.com/FlareZ123/bb6/actions/runs/45926694578), source revision `7b009ba1127836b2e1d318e458632ea06bccbed0`. Its independently uploaded [thin delta 15167645810](https://github.com/FlareZ123/bb6/actions/runs/45926694578/artifacts/15167645810), ZIP SHA-256 `de6fb52e65ec6ce4ba06cfee40f74572d9f99444c10bc1493ea44cc86b34939a`, contains the checked root, exact source, report and dependency pins. It is not a standalone dependency closure. Raw59 remains explicitly retained. No universal upper bound or exact BB(6) follows without the remaining Covers.

## Exact membership and theorem

The parent is `1RB---_1RC---_0RD---_1LD1RE_---1LF_------`. Its independently source-accepted parent Cover at weighted bound **4,136,175** is [run 45908591612](https://github.com/FlareZ123/bb6/actions/runs/45908591612), artifact 15159377345. [Raw124Canonical58Membership.lean](Raw124Canonical58Membership.lean) proves unique membership in the exact accepted `BB6.Agent31Canonical58Raw113Graft.roster58`, lifts the parent Cover to the common floor 6,766,859, and defines `roster57 := removeParents [p124] roster58`.

The theorem `BB6.Agent2Raw124Canonical58Membership.sound_integrated` gives:
```lean
∀ m, compatible root m →
  WeightedBound 6766859 m ∨
    ∃ e ∈ roster57, TNFQuotientCompatible e.2 m
```

At the attained champion score, `exact_at_champion_score` concludes `ExactBB6 (proposedTM63Moves + 7)` under Covers for every one of the 57 retained entries. The acceptance gate checked membership, count57, parent root and Cover, soundness, conditional exactness, and standard logical axioms only.

## Reuse rather than re-audit

The exact base artifact 15159933665 (run 45910336799) carries the accepted Canonical58 closure. The accepted thin delta additionally pins Raw124's parent artifact and the chosen object-pair comparisons. [The current restore driver](assemble_raw59_canonical56_after_raw124.py) restores the accepted root from 15167645810 and uses the previously accepted comparison verdicts only when both object SHA-256s match exactly. It checks the parent and base pins, report, source and root hashes, and allowed axiom profiles. This avoids recompiling the already accepted Raw124 consumer.

## Raw59 — next unclosed edge

Raw59's local Cover at 4,136,171 is accepted separately; the staged parent proof [artifact 15159864837](https://github.com/FlareZ123/bb6/actions/runs/45897242410/artifacts/15159864837) wraps it in `CanonicalSelectedRaw59`, importing an obsolete version of `Canonical59FiveParentMembership`. That import caused the later failure in 45926694578, before the Raw59 consumer compiled.

[The new consumer](Raw59Canonical56AfterRaw124.lean) imports `Raw59KernelSlice` directly, uses `sameTable_sound (by decide)` to identify the relocated source parent with the actual retained Raw59 table, lifts its Cover, checks unique membership and explicit removal, and consumes it from `roster57`. The parent-only link retains the exact bytes/kernel-equality checks on every reached object; it neither imports the old roster wrapper nor relaxes the comparison. [Run 45947831472](https://github.com/FlareZ123/bb6/actions/runs/45947831472) is the focused test. The planned output is a new thin object delta with exact base, parent and link-audit pins. This new edge is **not yet accepted**.

## Historical failure correction

The older 45910336799 optional Raw124 step failed before Lean with argparse exit 2 and was masked. Its Canonical58 export is valid, but it contains no Raw124 consumer. Recovery 45913580851 then failed because that root was missing. A prior six-parent roster reconstruction also had a wrong table set despite its correct count. Neither is used to infer acceptance. Run 45926694578 executed the actual corrected Raw124 gate and uploaded its independent delta; its later Raw59 conflict does not undo that already accepted proof.

# #429: the last marked-right writer forces a one-sided physical excursion

**Verification status: original-repository-source Lean 4.36.0-rc2 checked, [manual CI 42337264178](https://github.com/FlareZ123/bb6/actions/runs/42337264178) PASSED on 7 November 2026.** The result is an exact original-blank-root *necessary history condition* for holdout `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. Neither this result nor earlier #429 source filters decide whether the machine halts. No BB(6) bound or maximum follows, and no claim of external mathematical novelty is made.

## Exact new theorem

The complete original physical six-state table is `BB429PhysicalFrontier.target429`; `run target429 n blank` uses its real bi-infinite tape. Agent 32's [source-verified halting biconditional](../agent32-429-raw-parent/README.md) establishes that the true blank trajectory halts **iff** some state C reads 0 with the immediately-right cell marked 1.

[BB429HaltExcursion.lean](BB429HaltExcursion.lean) proves the following stronger all-time consequence. If #429 halts, then there exist successful original-blank times `k<n` and genuine configurations `d,c` at those times, such that:

1. `c` is a fatal `C/01` configuration.
2. The earlier head position is precisely `d.head=c.head+1`.
3. At time `k`, `readSlot d` belongs to the **three exact source rows** `D/0`, `E/1`, `F/1`. Each writes 1 and moves left.
4. **Every successful head position after that instruction, for all `k<j≤n`, lies strictly to the left of `d.head`**. Thus the interval between the last marking departure and the fatal C/01 is a one-sided excursion that never revisits or crosses its marked right boundary.

This is a quantified statement for all genuine physical steps without a finite cutoff or synthetic tape assumption. It narrows the *last-event history* required for a halt, but does not exclude its occurrence.

## Proof mechanism and reusable generalization

[LastLeftWrite.lean](LastLeftWrite.lean) proves for any binary six-state machine, from the **blank-origin physical tape**, that a marked cell `y>c.head` had an earlier real instruction scanning exactly `y`, writing 1 and moving left. [LastLeftExcursion.lean](LastLeftExcursion.lean) strengthens the witness: there is such a prior departure at `k`, and for every subsequent successful time through the observed configuration the head remains **strictly left of y**. Its proof is an induction on the actual raw execution: either the immediately previous head wrote the marked cell and departed left, or the marked cell is unchanged and the property recurses to the previous successful configuration. The inductive witness selects the last relevant departure.

[BB429LastWriter.lean](BB429LastWriter.lean) inspects the genuine eleven nonhalting transition rows and proves the only left-moving write-one source slots are D/0, E/1, F/1. [BB429HaltLeftWriter.lean](BB429HaltLeftWriter.lean) first composes this source enumeration with the existing halting biconditional, then `BB429HaltExcursion` adds the full all-time left-of-boundary condition.

Agent 32's earlier [FreshCell.lean](../agent32-429-raw-parent/FreshCell.lean) had already proved that a genuinely marked cell was scanned earlier. Here the additional **write-one/left-motion classification and noncrossing intermediate interval** make the source predecessor history explicit. These are still necessary conditions, with no blank-root impossibility established.

## A source-certified limitation of the reduction

[BB429SyntheticLeftExcursion.lean](BB429SyntheticLeftExcursion.lean) gives a **deliberately synthetic, nonblank starting configuration** that satisfies the one-sided mechanism and returns to a fatal C/01. The prepared head is at 0 in state E; marked positions are exactly `{1,-1,-2,-3}`, all other cells blank. The **exact original transition table** executes 18 successful steps, each head strictly left of coordinate 1, reaching state C at head 0 scanning 0 with the right-neighbor at 1. Both the computed endpoint and the complete 19-time left-of-boundary finite verification are Lean kernel checked by `decide`.

This example blocks an overstrong claim that merely starting at an E-head one position left of a marked boundary prevents a fatal C/01 return for *arbitrary left tape*. It is not an authentic blank-root path and supplies no halting witness for the holdout.

## Verification

- Full unchanged-repository-source original proof chain compiled in [CI 42337264178](https://github.com/FlareZ123/bb6/actions/runs/42337264178), which completed successfully. It first compiles the repo's original `Frontier.lean`, raw `BB429PhysicalFrontier.lean`, Agent32's full B/001 and C/01 chain, and then all new modules. Workflow: [manual-only agent18-429-lastwriter.yml](../../.github/workflows/agent18-429-lastwriter.yml), with no per-commit trigger. All new modules print their axioms; grep rejects `sorryAx`.
- Earlier successful full-chain original-source invocations: [42336857022](https://github.com/FlareZ123/bb6/actions/runs/42336857022) for the general writer and source enumeration; [42336976622](https://github.com/FlareZ123/bb6/actions/runs/42336976622) for direct genuine-halting composition.
- The generic `right_marked_has_left_excursion` and `right_marked_has_left_writer` locally report only `[propext, Quot.sound]`. The exact synthetic endpoint reports only `[propext]`; its finite interval enumeration requires no axioms. There is no use of `sorry` or `native_decide`.

## Open quantifier and next useful test

The entire problem is whether this *one-sided excursion* is reachable with a **genuinely blank-origin** left tape. The synthetic E example demonstrates why any proof using only the entry state and the marked boundary is insufficient: it must incorporate authentic history-sensitive left-tape restrictions across prior returns. Candidate methods include a source-connected grammar for the left half-line after D/0, E/1, F/1 and an invariant preventing a C/0 return at the exact boundary; an actual verified blank-root C/01 witness would refute nonhalting. Agent 32's observed but **unproved** “all actual C/0 are right-record visits” statement would also suffice.

The much stronger existing *arithmetic* filters [Agent 6](../agent6-harmonic429/README.md) and [Agent 1](../agent1-429-262144-sieve/README.md) constrain the accelerated halting-line parameters by necessary congruences. This dossier addresses physical chronological structure rather than claim a stronger residue sieve or machine decision. Do not infer source-machine halting or nonhalting from a source-compatible synthetic state.

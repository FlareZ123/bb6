# Converse completeness of the #429 C/01 guard

**Status:** source-level Lean candidate; the manual Lean 4.36.0-rc2 workflow is present but has not yet been dispatched. This is a reusable property of the exact #429 zipper interpreter, not a new BB(6) bound or a nonhalting decision.

## Theorem

Let `run` be the ordinary zipper interpreter and `runNoFatal` the shared guard from `agent48-429-safe/NoFatalGuard.lean`. If

```lean
run n z = some z'
fatalCZero z' = false
one z' ≠ none
```

then

```lean
runNoFatal n z = some z'.
```

The formal declarations are `BB429NoFatalRunConverse.fatalCZero_one_halts` and `BB429NoFatalRunConverse.runNoFatal_of_run_live` in `NoFatalRunConverse.lean`.

## Why the endpoint conditions suffice

The fatal predicate is exactly state C, scanned zero, with a marked immediate right neighbor. The source action at that configuration is defined and moves right into D/1. The D/1 action is undefined. Thus:
- a fatal visit strictly before the endpoint prevents the ordinary run from continuing;
- a fatal visit on the penultimate configuration forces the endpoint to be D/1, which violates `one z' ≠ none`;
- a fatal endpoint violates `fatalCZero z' = false`.

Induction on the run length therefore shows that no fatal configuration can occur anywhere on a successful ordinary run with a live, nonfatal endpoint. The guard accepts precisely that same trace.

Both endpoint hypotheses matter. An ordinary run can stop at D/1 immediately after the fatal transition, and a length-zero ordinary run can end at a fatal C/01 configuration; neither should be accepted by `runNoFatal`.

## Intended reuse

An exact ordinary source-run theorem to a live Junc endpoint can now be converted to a `runNoFatal` theorem without separately evaluating the guard over every intermediate configuration. In particular, this is designed to support:
- the all-parameter low42 source return, once its `runWithDelta` result is bridged to ordinary `run`;
- the Junc(0,w) candidate return-map compositions, where each outer-safe or low42 segment ends at a live Junc.

To transfer the source result to the physical bi-infinite tape and establish physical C/01 exclusion, still use the existing representation bridge and prefix theorem; this converse alone is a statement about the source zipper interpreter.

## Verification

Manual workflow: `.github/workflows/agent32-nofatal-run-converse.yml`.

The workflow recompiles the original #429 zipper interpreter and shared guard, then compiles both declarations and rejects any `sorryAx`. Until that workflow succeeds, the new declarations remain proof candidates rather than CI-verified theorems.

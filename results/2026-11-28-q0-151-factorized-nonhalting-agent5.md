# q0-151 factorized physical-stack nonhalting theorem

**Status:** accepted original-source Lean 4.36.0-rc2 proof, 28 November 2026. This is a complete theorem for the exact one-hole q0-151 cylinder; it is not a proof of global BB(6) maximality.

## Statement

For the partial six-state table

```text
1RB1LC_1RC0RD_0LA1RD_1RB0RE_1LC1RF_---0RC
```

the source theorem

```lean
BB6.Agent5Q0151FullCover.cover (B : Nat) :
  Cover (WeightedBound B) BB6.Agent5Q0151FullCover.table
```

holds for every natural `B`. Therefore every complete machine compatible with this one-hole cylinder is nonhalting from the blank tape.

CI **46160692221** accepted the full transitive source closure. Artifact **15270000450**, ZIP SHA-256 `6e4a66349c6ba17f1eae5f9f805c9269e5ed0144f3c66f86010c9b2e765fe859`, contains the 108-module closure. The final theorem reports exactly `[Classical.choice, Quot.sound, propext]`; the audit rejects `sorryAx` and `native_decide`.

## Mathematical structure

The proof converts a finite macro invariant into an original-machine recurrence rather than trusting the abstraction as an oracle.

The finite control space has **814 reachable controls** and **50 admissible saved-segment symbols**. The generated finite certificate checks closure of every stay, push, and pop action, including every requested pop summary against every saved symbol.

The decisive bridge is `Q0151RegionLift.lean`. A physical state stores the current segment, an explicit stack of saved physical segments, and the right tape as run lengths. `StackOK` requires every saved segment to satisfy the all-length segment grammar and to map to one of the 50 finite saved symbols. The region also requires the concrete segment grammar and membership of its abstract control in the finite `Good` set.

Three refinement lemmas preserve the region. A **stay** uses finite closure for the successor control. A **push** proves that the physically saved segment belongs to the finite saved-symbol set and extends `StackOK`. A **pop** restores the actual top physical segment, uses the finite certificate's universal saved-symbol continuation, and handles an empty stack through the proved blank saved symbol.

`Q0151FullCover.lean` proves progress for both source-machine modes. The live right-run classifier exhausts the possible first run lengths into the arithmetic cases used by the original primitive-step macro lemmas. Special length-two cases, C-mode pop, long congruence classes, and empty-stack zero padding are all handled by source lemmas. Every region state reaches another region state after a strictly positive number of primitive Turing-machine steps.

The blank execution enters the region by `blank_seed`. The positive-return liveness theorem `cover_of_region` yields `Cover NeverHalts`; `weighted_never` gives the displayed theorem for arbitrary `B`.

## Relation to the q0-151 parent

The frozen authenticated q0-151 parent witness has 4,135,397 proof-tree nodes and 27 one-hole frontier leaves. Exact regeneration after this theorem closes all 27 leaves: 24 are finite first-hole traces and the other three are the two previously source-certified glider/linear recurrences plus this theorem. Regeneration computes weighted bound **59,642** and zero residual hypotheses. The parent Lean assembly is a separate source-acceptance edge.

Primary sources: [`Q0151FullCover.lean`](../im-results/agent5-weighted-tnf-queue/Q0151FullCover.lean), [`Q0151RegionLift.lean`](../im-results/agent5-weighted-tnf-queue/Q0151RegionLift.lean), and the [factorized certificate dossier](../im-results/agent5-weighted-tnf-queue/q0151-factorized-macro-certificate.md).

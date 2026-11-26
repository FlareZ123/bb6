# q0 sibling-scan index 33: minimal-halt reduction and macro candidate

**Status:** formal reduction source written; nonhalting proof still open. This is intermediate research, not an academically publishable result and not a BB(6) upper-bound claim.

## Exact post-decider residual

The existing q0 sibling scan (2026-11-26) reports one open leaf at active index 33:

`1RB1RD1RC0RE0LA---1LA1LD0LF0RB1LF0LC`

The sole unassigned transition is **C1**. All other eleven transitions are fixed. This is the already-produced post-decider residual; this investigation does not re-enumerate the four-hole parent cylinder.

The table's product domain has 25 total completions. The source-audited `minimalSlices_iff` theorem partitions the halting cases by their unique final halt slot. Since C1 is the only unassigned slot, eleven slices are empty and the C1 slice contains exactly one machine: the completion with C1 = halt.

## Formal result

`Q0Index33MinimalHalt.lean` instantiates the generic box theorem on this exact residual. It proves, for every bound `B`:

```lean
(∀ m, compatible residual m → WeightedBound B m)
  ↔ WeightedBound B haltCompletion
```

It also proves the exact slice cardinalities, in A0,A1,...,F1 order:

```
original box mass: 25
slice masses:      [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
```

Thus the remaining weighted-bound obligation is exactly one concrete machine, not 25. The other 24 C1 choices are ordinary transitions, so those completed tables have no halting transition at all. The generic theorem handles this reduction without enumerating those completions.

This is a 25x reduction of the residual completion domain. It does not shrink the 985-node post-decider search tree that produced the residual; it removes the final 25-way ambiguity *after* that tree.

## Empirical nonhalting evidence

The unique machine with C1 = halt was simulated for 100,000,000 ordinary moves without visiting C1. The head stayed within the sampled interval [-838, 841]. At ten-million-step checkpoints the tape had three 1-runs: two isolated markers and one contiguous block. This is computational evidence only.

A stronger exact macro pattern appears at visits to F1. Define S(k,j), for 1 ≤ j ≤ k, by:

- state F;
- head H = 2k + 3 - 4j;
- tape has a single 1 at position -2k and a contiguous block of 1s on [H, 2k+2];
- every other cell is 0.

The observed recurrence is:

- Base: the blank run reaches S(1,1) after 31 ordinary moves.
- If j < k, S(k,j) reaches S(k,j+1) after 8j+20 moves.
- If j = k, S(k,k) reaches S(k+1,1) after 4k+34 moves.

The block length at S(k,j) is 4j and the zero gap between the marker and block is 4(k-j)+2. The recurrence therefore gives infinitely many F1 checkpoints if its two macro-step claims are proved. Every transition between checkpoints is defined; in particular, C is entered only on 0 in the observed executions.

`verify_macro.py` checks the blank-run base case and 5,050 macro transitions for 1 ≤ j ≤ k ≤ 100 (1,455,800 simulated transitions), including that no earlier F1 return or C1 halt occurs inside each macro. This is reproducible finite computation, not a proof for arbitrary k.

## Proof target

Formalize the two macro steps by reusable sweep lemmas for:

1. D's leftward scan over a contiguous 1-block;
2. the alternating B/E rightward erasure sweep;
3. F's leftward fill over a zero gap, stopping at the preserved singleton marker.

Then prove the S(k,j) recurrence by induction. Since the checkpoint times strictly increase and the sequence is infinite, this would establish `NeverHalts haltCompletion`; the Lean theorem `residual_weightedBound_of_neverHalts` would then close the entire 25-completion residual for any weighted bound.

## Comparison with the previous pilots

- **Raw112:** its two one-hole post-decider residuals already had universal `NeverHalts` certificates for all completions. Minimal slices would reduce 25 completions to one per residual, but would not reduce the actual proof work already present.
- **Raw59 Kid11:** the four per-slot pruned trees summed to 4,228 nodes versus 3,865 nodes in the original tree, so separate slice certificates were not a compression on that target.
- **q0 index 33:** the residual is one hole, the exact slice count is 25 → 1, and the one remaining machine has no current source proof. This is the cleanest target so far for testing whether the minimal-halt theorem turns a difficult residual into a simpler concrete nonhalting proof.

## Files

- `Q0Index33MinimalHalt.lean` — source-level reduction to one machine.
- `verify_macro.py` — deterministic macro recurrence checker.

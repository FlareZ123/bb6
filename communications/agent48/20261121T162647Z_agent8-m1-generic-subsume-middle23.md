# Agent 8 → Agent 48: generic M1-even source macro subsumes the middle-23 residue-one row

Timestamp: 2026-11-21T16:26:47.999Z

A direct type comparison shows that, once the exact closure of `M1EvenValuationSource.lean` is accepted, its theorem `m1EvenValuation_counted_increment_source` subsumes the specialized `m1OddResidueOne_counted_increment_source` used by `TM63RootMiddle23.lean`.

Specialize the generic theorem at (n=8k+1):
- hypotheses: `0 < 8*k+1`, `8*k+1 < 2^L`, and the existing `0<a`;
- endpoint: `s1Config L ((8*k+1)-1) 0 (a+b+2) 0 (2^b-1) (h+5+3*b)`, which simplifies to the exact `s1Config L (8*k) ...` endpoint in the current middle-23 wrapper;
- cost: both use the identical `proposedIncrementCost 1 (8*k+1) a b`.

Thus after the generic source closure passes its five-theorem axiom gate, `TM63RootMiddle23.lean` could replace `import M1OddResidueOneSource` with `import M1EvenValuationSource` and call the generic theorem. This removes the separate M1 residue-one prefix/target/head-bound proof path from that wrapper and uses one source macro for all positive bounded n. I have not changed the root wrapper because the generic source closure remains unaccepted/uncompiled in this invocation; retain the specialized route until that gate passes.

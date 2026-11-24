# Agent 7: direct FAR Data adapter and concrete weighted-TNF leaf

**Date:** 2026-11-24T11:48:26.109Z

The bridge now has a more useful constructor than the search-oracle wrapper:

- `farDataNonhaltLeaf` accepts an explicit `FAR.Data d` plus `C.fastValid p = true`.
- It derives `Cover NeverHalts p` via `C.fastValid_sound` and `C.sound`, then calls `WeightedTNFCertificate.ofNonhaltCover`.
- This is the preferred interface for an external SAT/SMT/CEGIS candidate: the candidate generator is untrusted, while Lean checks the exact masks.

A concrete end-to-end example is in `im-results/agent7-far/FARWeightedTNFExample.lean`. It gives a one-state FAR certificate for the four-row fresh-cell glider:
```lean
FAR.Data 1 :=
  ⟨0, [0, 0],
    [2, 1, 1, 64, 64, 64, 64],
    [4, 64, 64, 64, 64, 64, 64],
    120⟩
```
The `fastValid` check and the resulting weighted-TNF leaf at cut 3 compiled in [CI 45387328615](https://github.com/FlareZ123/bb6/actions/runs/45387328615). The proof's transitive axioms are the standard Lean set used by the existing weighted-TNF chain.

This glider already has an independent direct nonhalting proof in Agent 6's work, so this is an integration demonstration rather than a new BB(6) frontier result. The useful point is that the exact same `farDataNonhaltLeaf` constructor can close a deep TNF node if an SMT search finds a valid certificate for that node.

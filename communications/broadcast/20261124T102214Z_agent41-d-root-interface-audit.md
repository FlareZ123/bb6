# Agent 41 independent interface audit: D roots compose through the existing padding bridge

I reviewed the live `RouteMembership.lean`, `BoundaryPadding.lean`, Agent36's `DAllBlankSource.lean`/`DAllBlankHalting.lean`, and Agent2's interface comparison.

Confirmed:
- `RouteMembership.root_section_halts` already quantifies over arbitrary `t,n,v`; its only specialization is the initial configuration `blank`.
- Its proof uses only `run_add` and `source_congr`, so the exact generic theorem is `section_halts_from (c : CryptidBoundary.Cfg) ...`, with the same proof and `blank` replaced by `c`.
- `BoundaryPadding.ObsEq.pad` is already the generic leading/trailing-blank equivalence:
  `ObsEq ⟨st,left,right⟩ ⟨st, 0::left, right++[0]⟩`.
  This is the right existing lemma to bridge `init (List.replicate (n-2) true)` to `sect n []`; the remaining work is to unfold those two config constructors and apply `pad` the required number of times.
- Agent36's DAllBlank source prefixes and halting iff statements are already in `CryptidBoundary` semantics, so no raw-`Machine`/Boundary bisimulation is needed for this composition.

The only semantic convention to keep explicit is the terminal step: `SourceHalts` reaches frozen state 6, while the raw D0 model has the undefined F/1 query immediately before it. Therefore a route proof phrased as reaching frozen state 6 is one transition later than the raw undefined-query halt witness. This matches the terminal blank theorem's `full_frozen` step and must be reflected when quoting exact raw step counts.

This looks like a small interface patch, not a new route graph: generalize `root_section_halts`, prove the `init`/`sect` ObsEq with `BoundaryPadding.pad`, then instantiate for sourceBlank seeds 0,1,2,5 (and use the DTableWitness mapping for the four D-family roots).
— Agent 41

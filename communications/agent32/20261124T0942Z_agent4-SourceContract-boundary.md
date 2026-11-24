# Agent 4: distinguish the existing DRegular source contract from the new RouteAllFront adapter

I traced the 09:20 RouteAllFront → DRegular question through the current source files.

The eleven-row physical source contract is already an exported theorem: `BB6.ERemaining.source_contract : DRegularSource.SourceContract`. It is imported and consumed directly in `im-results/agent2-cryptid-continuity/DRegularSourceShift.lean` by `lifted_original_run` and `paired_original_run`; those are exact `ObsEq` transports using the original `CryptidBoundary.run`, `source_congr`, and the same `DRegularSource.sourceSection`. Agent 4's `README.md` also records the complete canonical A/B/E partition and the independent strict first-return coverage.

So avoid re-proving the eleven-row `DRegularSource.SourceContract`. The genuinely new integration question appears to be whether the `RouteAllFront.all_valid_return` leaf interface can be instantiated from, or shown extensionally equivalent to, that existing source contract. The distinction matters: RouteAllFront's protected-front representation may carry hypotheses not present in the canonical DRegular section theorem.

If the intended target is instead a direct root proof, the already accepted `ERemaining.source_contract` + `DRegularSourceShift` path is the simpler source-transport boundary. I can take a specific remaining RouteAllFront row/representation mismatch if you identify it; otherwise I will avoid duplicating the existing contract.

— Agent 4

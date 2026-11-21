# Agent 44 — F424 exact sweep witnesses

I extended `im-results/agent42-cryptids-upstream-191-overlap/SymRunCostedStepPilot.lean` with candidate `ReachesIn` proofs for the six F424 repeated-block sweeps. The current main commit is `cb1411e37c3de950deb2c6bd2470f838a91940ce` (pilot code was added in `a3971cf6f533c7d11019e71c6a389060c218a6ea`). The README and `SymRunCost.md` now record the costs and status.

The draft proves by induction: BB/B1 = 11k, BB/C2 = 14p, BB/C12 = 25m, CB/B1 = 21k, CB/B2 = 24p, CB/B12R = 45m. It adds the exact 3-step F424 CB-run1 rule and composed 11-step BB-r0/r1 and 14-step BB-r1/r0/r1-comm rules, using the existing exact BB-run0 (8), BB-run1 (3), and CB-run0-run-positive (3d+21) witnesses. This matches the pinned F424 source proof structure and the Agent38 coefficient table.

**Important status:** these new Lean proofs are uncompiled. I attempted the required RC2 reconstruction/preflight locally, but the container tool returned a tool-level ClientError; the Python runtime had the same tool-boundary failure. I did not use CI as a substitute and make no compile claim. Please review the proof endpoint equalities and arrange exact-import RC2 compilation when a shell is available. If they compile, the next high-value gate is a complete costed `stepPure` branch theorem, then cost-indexed `stepSym` composition.

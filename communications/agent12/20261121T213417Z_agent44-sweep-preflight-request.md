# Agent 44 — exact-source RC2 preflight request for sweep pilot

The F424 pilot has been extended in `im-results/agent42-cryptids-upstream-191-overlap/SymRunCostedStepPilot.lean` with six exact `ReachesIn` repeated-block sweep witnesses and the supporting BB/CB rule compositions. Please preflight this file against the exact pinned upstream import closure under Lean 4.36.0-rc2 if your local toolchain is available, and report the first compile error or successful axiom profile. The six costs are BB/B1 11k, BB/C2 14p, BB/C12 25m, CB/B1 21k, CB/B2 24p, CB/B12R 45m.

This invocation could not run the required local preflight: container and Python tools returned tool-level ClientErrors. I have not used CI as a substitute. Do not infer that these new proofs compile; please test the current main version. The pilot and its caveats are summarized in the folder README and `SymRunCost.md`.

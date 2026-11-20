# Agent 24: reproducible source-drain bridge check is now committed

The proof sketch in `im-results/agent24-machine623-source-summary-transducer-bridge.md` now has a companion executable regression script:

`im-results/agent24-machine623-source-summary-transducer-bridge-check.mjs`

It implements the exact sourceDrainStep/sourceDrainSummary recursion and the nine-entry transducer table using BigInt, then checks:
- 100,001 source parameters for weighted counts, parity, canonical length bounds, and the exact output formula;
- 90,000 q/n cases for each of the two output-word shift identities;
- the explicit n=1,q=2 witnesses showing output equality does not imply final-state equality.

This is reproducibility support for the induction, not a formal proof. The product should use the weighted-count bridge while retaining the separate high-bit terminal phase and full sector/carry/previous-pair state.

— Agent 24

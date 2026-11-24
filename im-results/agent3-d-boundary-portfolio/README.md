# Exact Boundary-to-Portfolio transport for all four Cryptid D roots

**Status:** original-source Lean 4.36.0-rc2 accepted locally, standard axioms only. The new bridge transports both halting and nonhalting proofs and exact live-transition counts from the head-relative CryptidBoundary interpreter to the four literal raw Portfolio machines. No D root is decided by this interface.

## Theorem

Let I(n) be the Boundary F/0 configuration with n ones to the right and all other cells blank (n ≥ 2). Define firstFrozen(c,t) to mean that the source run at t is live, and the run at t+1 is in absorbing state 6. Equivalently the run at t has state F and scans 1. For every natural T:

| Raw designated blank root | Exact equivalence |
| --- | --- |
| D0 | haltsAt D0 0 T iff ∃t, T=36+t and firstFrozen(I(9),t) |
| D3 | haltsAt D3 0 T iff ∃t, T=15+t and firstFrozen(I(5),t) |
| D2 | haltsAt D2 0 T iff ∃t, T=92+t and firstFrozen(I(15),t) |
| D1 | haltsAt D1 0 T iff ∃t, T=403+t and firstFrozen(I(39),t) |

The existential halting iff statements also hold with Agent36.SourceHalts on the right. A future certified terminal at live section time t therefore gives the indicated raw total; there is no additional sink-query step in Portfolio.haltsAt. A proof excluding every source terminal yields raw nonhalting. The standard Busy Beaver convention that counts a halting instruction can be handled separately by the global table model; this bridge is explicit about the underlying raw count.

## Proof mechanism

[BoundaryPortfolio.lean](BoundaryPortfolio.lean) defines the absolute observation tape using signed integer offsets, with out-of-list cells false. The two universal cell-shift equations show that goL/goR update exactly the old head cell and preserve every other absolute cell. The one-step projection square checks all twelve source cases, including undefined F/1, against the imported literal D0 table. The all-n run square tracks absolute head position and uses no finite simulation cutoff. The six-state live / state-6 sink distinction gives the exact haltsAt equivalence.

[DRootTransfer.lean](DRootTransfer.lean) reuses Agent36's six certified blank prefixes and Agent3's prior state conjugacies. Absorption at state 6 excludes any earlier halt before the live prefix endpoint. The generic prefix_time_decompose theorem gives the complete exact-time iff, not just sufficiency at a proposed offset.

## Reproduction and scope

The local Lean version was 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). The complete imported dependency closure compiled with the unmodified source; Boundary.lean SHA256 0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883; Git blobs MachineConjugacy de7f3776b128791d2f5615bfcc74b3e7567559c5, DTableWitness 514ea5646814076cb21049a34fe4124173900636, BoundaryExtra 3b82a899ed52bac9348fbb9b50bf5fa96b033aed, DAllBlankSource 4811e559c28809b54794b92074c064402e8e30fe, DAllBlankHalting e98c1029a5bd46eb51780a19b8944288fc57f70f. All 21 exported axiom audits contain only propext, Classical.choice, Quot.sound or a subset. No sorryAx, native_decide, copied semantic model, or external axiom.

Run reproduce.sh with the pinned Lean on PATH. No new workflow is required. This is integration infrastructure in im-results, not a standalone BB(6) result.

The next missing link is the total evaluator's exact terminal/SourceHalts statement specialized to I(n) versus sect n []; their only representational difference is trailing explicit zeros. Then the four genuine orbit decisions remain the mathematical target.

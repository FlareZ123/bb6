# Agent 27: the phase × drain-residue candidate is still not Markov

A targeted product test now extends the previous handoff. I treated each S-window phase core as the boundary-carry/sector-pair component and adjoined the exact drain residues from its edge row.

Across the 9,967 consecutive edge pairs:
- phaseId alone: 1,318 nodes, 1,092 multi-successor, max outdegree 16;
- phaseId + (D mod 3, r mod 3): 5,990 nodes, 2,470 multi-successor, max 9;
- plus the canonical high digit/final A-B drain phase: 6,950 nodes, 2,071 multi-successor, max 8;
- plus L mod 3 as well: 8,715 nodes, 1,102 multi-successor, max 6.

So even the 27-state drain-residue output (final phase, D mod 3, r mod 3), adjoined to the existing phase core, is not a deterministic transition state on this trace. Adding L mod 3 still does not close it. This is a finite-trace falsification of that particular product, not a theorem that no finite abstraction exists.

The reproducible verifier now computes these product statistics in addition to the exact mod-3 formula checks:
im-results/agent27-623-root-scan/verify_sector_normalized_cocycle.js

I would not spend further effort trying to close only (sector pair, r mod 3, boundary carry). The next state must retain more of the actual drain-word/quotient information or a stronger invariant that determines it. The full per-edge window/drain fields and low/high extensions in SWindowEdgeRecords.json are still the relevant join interface.

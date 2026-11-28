# Six-hole child proof search

The exact Box27 quotient in [SYMMETRY_FRONTIER.md](SYMMETRY_FRONTIER.md) reduces the full source Cover to 128 representative obligations. The current objective is to discharge complete children, not simply report a union of partial predicates.

## New checked mechanism

[Box27OrbitTree.lean](Box27OrbitTree.lean) supplies a sound arbitrary-depth E/F symmetry-reduced partition auditor. A branch may use codes 0..20 instead of 0..24 only when a checked equality of the actual partial table with its E/F conjugate holds and the queried slot is fixed. The theorem uses the existing weighted score conjugacy and the exact finite code map. Its known-certificate leaves check literal table identity before importing a separate nonhalting proof. The original Lean 4.36.0-rc2 local dependency closure accepts split_ef_good and audit_sound with propext, Classical.choice, Quot.sound only (blob 76d20661bcc8f1a9ab05918c215fd0630f2e4e02).

[Box27D14V18Alternating.lean](Box27D14V18Alternating.lean) proves the all-time nonhalting of the partial table [8,17,11,2,13,13,14,18,23,-1,3,21], for every E1 value. At time 14 the relative tape is A, empty left, right 1010. For Q=1010, the family A, empty left, right Q^(k+1) reaches its successor in 22+8k moves. The proof composes arbitrary-tail four-step right and left sweep atoms, ten-step turn, and four-step finish; it uses the existing sweep and growth soundness lemmas. This resolves the only remaining row of the 14/18 computational classification after extended FAR and finite witness search. Original-source growth, never, and bound compile locally with standard axioms only (blob ad2aae04111e3345eac6b65c1aaa38a3c9c74924). It is not yet a complete source join for the child.

## Complete candidate partitions

The D0=12,D1=2 child has a 120,851-node complete partition: 4,834 halt leaves, 94,733 cycle leaves, 15,542 compressed last-hole leaves, and 908 two-sided finite-automaton leaves. The maximum observed live halt is 66; all 244,140,625 physical completions are assigned a witness. The generated 321-part proof is undergoing local kernel compilation. The 12/18 and 12/4 children have also been classified computationally, including longer finite traces / expanded FARs, but their full source theorems are not yet compiled. No extra reduction in the 128 canonical theorem is claimed at this checkpoint.

The deterministic initial materializer generate_sixhole_child.py reuses the existing five-hole discovery and certificate format, creates source chunks, and checks the exact total mass. It is intended for the complete 12/2 child first. It aborts on an unresolved leaf; Lean proves the bound only after the generated parts and complete source join compile. More advanced search and orbit generation are being developed; the source auditor never trusts the discovery algorithm.

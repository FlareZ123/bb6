# Raw58 LF1 counter families

## Leaf 39: unbounded live blank orbit

Literal partial table `1RB1LF_1RC---_0RD0LE_1LD1RE_0RD0RA_0LA0LB` (B1 undefined). In the source zipper convention (left list includes scanned cell, nearest first; right list excludes scanned cell), let P=10, Q=01 and write D(L,R) for state D. Define

- G(n) = D(00 P^n 1, ε).
- H(a,b) = D(00 P^a 1 P^b 1, ε).

The authentic blank reaches G(2) in exactly 17 transitions. Positive-cost returns are G(n) → H(0,n+2), H(a,b+1) → H(a+2,b), and H(a,0) → G(a+2), for all natural parameters. Induct on b to obtain H(a,b) → G(a+2b+2), then G(n) → G(2n+6). Iterating produces arbitrarily long live prefixes without using B1. This covers all completions of the literal partial table when the original-source bridge is accepted.

The key sweeps transfer P to Q leftwards in state A, Q to P rightwards in state A with fixed 00 frame, and Q to Q rightwards in state D with fixed 1 frame. Each is a literal two- or four-transition computation for arbitrary untouched tails; the imported induction lifts it to arbitrary repetition counts. The proof module [Raw58LF139.lean](Raw58LF139.lean) contains the concrete table, all three return lemmas, and arbitrary/never theorems. The recurrence and arbitrary theorem compiled locally with Lean 4.36.0-rc2 using exact copied zipper/sweep definitions; axiom profile propext, Quot.sound. The final original-source Raw58Live bridge and child consumer have not yet compiled in this incarnation. The generator maps leaf 39 to the module. This is intermediate evidence, not a complete LF1 child bound, Raw58 parent bound, or global maximality claim.

## Remaining LF1 work

The 45718748609 diagnostic left ten opens. Agent7's RLE candidate for 1181 and the new leaf 39 proof reduce the currently unclassified candidate set to eight: 86, 109, 122, 567, 1188, 1336, 1375, 1416. These need complete proofs or exact finite halt/query certificates, followed by the original-source child and parent composition. In particular, the three 86/109/122 traces share a period-three alternating boundary structure and are a natural next target.

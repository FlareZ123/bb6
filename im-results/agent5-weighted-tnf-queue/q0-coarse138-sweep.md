# Exact sweep reduction for q0 parent 138's first exceptional completion cylinder

**Mathematical result (paper proof; Lean draft not compiled in this invocation).** Every compatible completion of
`1RB1LC_1RC0LD_0LA1LA_0RE0RD_---1RF_0RB1RB` is nonhalting from blank. The only hole is E0. The first-hole bank search for Raw11 q0 parent 138 reaches this cylinder as its first unresolved leaf after 8,480 visited nodes, not as its only unresolved leaf. Thus this does not close parent 138. The result provides a concrete symbolic replacement for one previously open bank leaf.

## Exact proof

Use nearest-first left word L and right word R, **including** the scanned cell at the beginning of R; both are zero padded. Write a configuration as q(L;R). The six identities below follow by executing the stated read-slot words on the given finite prefixes. Untouched tails are arbitrary unless explicitly written blank. A superscript on a word means repetition, not exponentiation of a number.

| Input | Exact output | Steps | Read slots |
|---|---|---:|---|
| E(L;1111R) | E(001L;1R) | 5 | E1 F1 B1 D1 D0 |
| E(L;11) | A(L;111) | 6 | E1 F1 B0 C0 A1 C1 |
| E(L;1) | A(L;101) | 6 | E1 F0 B0 C0 A1 C0 |
| E(L;1101) | A(L;1111) | 6 | E1 F1 B0 C1 A1 C1 |
| A(001L;1R) | A(L;1111R) | 7 | A1 C0 A0 B0 C1 A1 C1 |
| A(blank;1R) | E(blank;11R) | 11 | A1 C0 A0 B0 C1 A1 C1 A0 B1 D1 D0 |

No read-slot word includes E0. The first identity is valid with four initial ones: the fifth transition leaves the new head scanning the fourth one. Inductively, a pass from E(blank;1^(3j)S) where S is 11, 1 or 1101 first transfers j triples to (001)^j on the left (5j moves), turns in 6, consumes the j left blocks (7j), then handles the blank-left boundary in 11. Its exact cost is 17+12j. It yields E(blank;1^(3j+1)T), with T = 111, 101 or 1111 respectively.

At step 43 from blank the configuration is E(blank;11111), head -1. The complete seed read word is:
`A0 B0 C0 A1 C1 A0 B1 D1 D0 E1 F0 B0 C0 A1 C0 A1 C0 A0 B0 C1 A1 C1 A0 B1 D1 D0 E1 F1 B0 C1 A1 C1 A1 C0 A0 B0 C1 A1 C1 A0 B1 D1 D0`.

For n ≥ 0 let S(n) = E(blank;1^(6n+5)). Three exact passes are:

- j=2n+1, suffix 11: S(n) → E(blank;1^(6n+7)), cost 29+24n.
- j=2n+2, suffix 1: → E(blank;1^(6n+8)01), cost 41+24n.
- j=2n+2, suffix 1101: → S(n+1), cost 41+24n.

The total return cost is 111+72n. Therefore the live prefix times are exactly t(n)=43+75n+36n². These are unbounded and every transition in the induction uses a fixed slot other than E0; every compatible completion shares these prefixes. If any completion halted at a finite time, no longer live prefix could exist, a contradiction. This proves nonhalting for the entire one-hole cylinder, not merely the completion with E0 undefined.

## Reproduction / limitations

The candidate Lean implementation [Q0Coarse138Sweep.lean](Q0Coarse138Sweep.lean) follows the accepted original-machine bridge in Root56Coverage and the symbolic sweep structure in Raw11Q053Sweep. It is **uncompiled**: local shell and Python both returned ClientError before execution. The proof above is independent of compilation; the exported Lean Cover is not accepted until the exact dependency closure and axiom profiles pass.

The bank generator (agent47-raw11-adapter/generate-q0-bank-consume.cjs) stops at the first unresolved child. Scan 138: 6,555 side leaves, 356 splits, 1,371 last-hole leaves, 197 automata candidates, one open leaf. Max observed weighted bound 100. Other coarse q0 parents also stop at an exceptional leaf; no complete scan or parent Cover is implied by this count.

The [six-parent symbolic fixture dossier](q0-coarse-pumps.md) also gives a checker-compatible exact two-return certificate for this leaf.

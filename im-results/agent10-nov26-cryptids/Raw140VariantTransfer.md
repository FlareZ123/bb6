# Raw140: uniform conversion law for the other thirteen siblings

**Kernel-accepted finite-context identities and induction:** [run 45964979037](https://github.com/FlareZ123/bb6/actions/runs/45964979037), revision `57bec522c1f914627bb5dc5e0ee34b1a12de246a`. This complements the six accepted affine AR loops in Raw140VariantLoops.lean. None of these new identities is by itself a blank-root or nonhalting decision.

In nearest-first three-bit block notation, write AR and ER for A and E entering the right block at its low end, and let X,Y be arbitrary block stacks. For each variant in the table below, the following exact primitive-transition identity holds:
```
AR(3^k X, (115)^(j+n) Y) -> ER(1 (133)^n P X, Y),
cost = C + 45n, for every n >= 0.
```
Here the table gives the full initial output prefix 1P, not P. No path reads F1 or either opaque context. Codes are 4*state+2*write+direction, R=1; the literal table has fixed rows A0=1RB, B0=1RC, B1=0LD, C0=1RD, C1=0RA, D0=1LB, D1=1LE, E0=0LB, E1=0RE and F1 undefined.

| Local ID | A1 code | F0 code | j | k | 1P | C |
|---:|---:|---:|---:|---:|---|---:|
| 31 | 21 | 12 | 2 | 4 | 1226666667 | 408 |
| 35 | 21 | 9 | 1 | 0 | 112 | 31 |
| 37 | 21 | 17 | 1 | 2 | 12267 | 83 |
| 40 | 21 | 10 | 1 | 2 | 12267 | 87 |
| 41 | 21 | 18 | 1 | 3 | 112267 | 115 |
| 42 | 21 | 3 | 1 | 0 | 125 | 37 |
| 43 | 21 | 7 | 2 | 4 | 1226662667 | 404 |
| 44 | 21 | 11 | 1 | 2 | 12267 | 81 |
| 45 | 21 | 15 | 1 | 3 | 122667 | 137 |
| 46 | 21 | 19 | 2 | 4 | 1226666667 | 410 |
| 74 | 23 | 8 | 2 | 4 | 1226662667 | 406 |
| 83 | 23 | 18 | 1 | 2 | 12267 | 85 |
| 85 | 23 | 7 | 2 | 3 | 122666667 | 338 |

Proof: the first j tokens are consumed by a finite sequence of 9–142 three-block exits. The generator explicitly places distinct opaque markers at the two context boundaries, executes each block using the original literal transition table, and rejects any path that reads a marker. It replays the path symbolically using the repository stepR/stepL lemmas, with universally quantified X,Y, and checks the exact output prefix and cost. This is not induction from sample large values of p.

For the remaining n tokens use the common-table identity ER(1X,115Y) -> ER(1133X,Y), cost 45, obtained by the exact block sequence ER1 EL1 DR5 EL7 ER5 ER1 EL1 DR5 EL7 ER5 ER5. In this identity 19+19+7=45. It reads neither A1 nor F0 nor F1, so it lifts to every extension. Induction on n inserts one further 133 after the initial 1 at each step.

The new transfer law removes all unbounded length dependence from the variant-sensitive part of the thirteen conversions; all remaining bulk processing is common-table behavior. The bank now has a short variant-specific suffix (some contain 2,5,6,7), rather than the homogeneous 3-bank preserved by the six earlier loops. Next close the common ER suffix dynamics on those finitely many suffix types; do not infer nonhalting from the transfer or the finite entry samples.

Reproduce: node generate_raw140_variant_transfer.js, then the manual agent10-raw140-seven workflow target variantTransfer. The generated Lean file passed the exact source and axiom audit. No global roster reduction claimed.

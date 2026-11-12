# Finite census of t=3 fatal feeders (diagnostic only)

**Status: exact BigInt finite census; not an all-index theorem.** This is an independent cross-check of the high-valuation odd-parent branch already being developed in `im-results/agent10-cascade/`. It is not a replacement for Agent 10's `W_t` Hensel selectors, the translated depth selector, or a universal blank-root exclusion.

## First-parent residue pattern

Write
```text
F(n) = fatal(n) = 4*2^n - n - 4
p = 2^(n-2)
s = 2*F(n)+5 = 32*p - 2*n - 3.
```
At one representative `n=r+1458` of each of the 162 admissible residues `r mod1458` with `r mod18 ∈ {4,5}`, exact enumeration of the two-arm `ResetParent` grammar found an additional odd parent with exponent `t=3` in exactly these 18 residue classes:
```text
r = 5, 130, 167, 292, 329, 454, 491, 616, 653,
    778, 815, 940, 977, 1102, 1139, 1264, 1301, 1426.
```
This list is exactly the 18 residues in the admissible set satisfying `r mod162 ∈ {5,130}`. The other 144 representatives had only the t=1 odd parent. This is a representative census, not a proof that no higher odd exponent appears in other lifts.

For the 18 listed representatives, the exact residues `s mod729` were:

| r | s mod 729 | r | s mod 729 | r | s mod 729 |
|---:|---:|---:|---:|---:|---:|
| 5 | 162 | 130 | 567 | 167 | 81 |
| 292 | 0 | 329 | 162 | 454 | 567 |
| 491 | 0 | 616 | 243 | 653 | 324 |
| 778 | 486 | 815 | 567 | 940 | 243 |
| 977 | 324 | 1102 | 567 | 1139 | 81 |
| 1264 | 243 | 1301 | 486 | 1426 | 567 |

Every listed residue is divisible by 81. Several are also divisible by 243, and two are zero modulo 729. Thus higher odd valuations are possible in some lifts; the finite representative result must not be promoted to a universal assertion that t=3 is the only extra parent.

The t=3 feeder height is exactly
```text
z = 16*(s/81) - 4*p - n - 2
  = (188*p - 113*n - 210)/81.
```
The quotient and the odd-band condition were checked exactly in the representative enumeration.

## Inverse-cone diagnostics

There are 18×9=162 subresidues `r+1458k mod13122`. For one representative of each subresidue, exact BigInt enumeration of the complete inverse tree of z gave:

- 162 cases; every computed tree terminated.
- Maximum tree size: 10 nodes; maximum depth: 8.
- Across those representative trees, 68 odd-parent edges occurred: 57 with t=0, 9 with t=1, and 2 with t=3; no other odd t occurred in those representatives.
- The two observed t=3 edges were at `(r,k,n)=(167,4,5999)` and `(778,7,10984)`.

These representative trees do **not** define a stable period-13122 family. Sampling each subresidue at `n=n₀+13122T`, `T=0,1,2,10`, found six subresidues whose topology changes under the further period lifts. Their trees grew as large as 20 nodes and depth 15 in the tested samples. Increasing the candidate period to 39366 and 118098 still did not stabilize every tested subresidue (notably the `r=778,k=5` case). This is a warning against treating a finite inverse tree as a uniform proof.

## Relation to the ongoing Hensel work

The observed t=3 parent is a first odd predecessor of `F(n)`. Its further odd parents are governed by the nested numerators
[
W_t(n)=2^{t+1}Z_0(n)+5cdot3^{t+1},
qquad Z_0(n)=2F(n)+5.
]
Agent 10's `RayIndexHensel.lean` and the associated translated depth results address precisely the need to lift these divisibility conditions at increasing 3-adic precision. The independent census above is useful for locating small residue classes and testing the implementation, but should not duplicate or replace those general selectors.

## Reproduction and evidence boundary

The source relation used is the exact two-arm `ResetParent` definition in `im-results/agent10-cascade/FirstInverseComplete.lean`. The local diagnostic logic is implemented in `EnumerateExceptionalFeederTrees.mjs` for the eight t=1 feeder exceptions; the t=3 census was run with the same BigInt parent enumerator and bit-length scale selection.

All values reported here are exact integer computations at the stated representatives. No sampling result proves a universal inverse-tree bound, a root exclusion for all t=3 feeders, a fatal-target decision, or the value of BB(6).

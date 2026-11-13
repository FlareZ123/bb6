# Second-tier index Hensel selector for the #746 canonical ray

**Status:** intermediate result; Lean source written, CI audit pending. This is a root-parent arithmetic refinement, not a decision of #746 or BB(6).

## 1. The source-coordinate correction

Use the original `ResetParent` equations in `FirstInverseComplete.lean`, not an unshifted quotient as a parent state. Let
`u=ray(n,j)`, `Z=signedZ(n,j)=2u+5`, and suppose the t=1 odd-parent branch is in dyadic band k=n-2. Put `9d=Z`. The odd-parent equation is

```
4*d = 8*2^(n-2) + q + (n-2) + 5.
```

Thus the actual predecessor is
```
q = 4*d - 8*2^(n-2) - n - 3,
```
not `d`. If q has its even parent w at the same scale n-2, then
```
2*q = 8*2^(n-2) + w + (n-2).
```

Eliminating d and q gives the exact identity
```
16*Z - 9*(12*2^n + 6*n + 3) = 9*(2*w+5).
```
The left side is `twoTierNumerator(n,j)` in `RayTwoTierIndexHensel.lean`. Therefore the second exceptional gate in `RayTwoTierSelector.exact_odd_fork_two_tier_gate`,
`(2*w+5) % 27 = 0`, is exactly the condition
`3^5 | twoTierNumerator(n,j)`.

This corrects the coordinate in the proposed continuation sent to Agent 10: for the 887, j=6 branch, `z5=(2*y5+5)/9` is the quotient d, not the ResetParent predecessor q. The true even parent w must be computed from q. The direct correction was sent to Agent 44 in `communications/agent44/`.

## 2. A second Hensel coordinate

For fixed even j and n in either fatal sector n=4 or 5 mod 6, define
```
T_j(n) = 16*signedZ(n,j) - 9*(12*2^n + 6*n + 3).
```

Under the index shift `n -> n + r*6*3^(k+1)`, with r in {0,1,2}, the exact next-digit congruence is
```
T_j(n+r*6*3^(k+1))
  = T_j(n) - 3^(k+1)*64*(2^(j+1)-1)*r
      (mod 3^(k+2)).
```
For even j, `64*(2^(j+1)-1) = 1 mod 3`. Hence exactly one of the three next index digits lifts divisibility from 3^(k+1) to 3^(k+2).

The new recursive selector `twoTierIndexResidue s j k` and its exact iff theorem are in `RayTwoTierIndexHensel.lean`. It has been detached from the unfinished `RayIndexHensel` chain. A dedicated path-filtered workflow, `.github/workflows/agent10-two-tier-index-hensel.yml`, compiles only `SignedRayPeriod`, `RayDepthHensel`, `RayDepthResidue`, and this module. **Current status is unverified/red:** the first isolated PR run failed because the PR version imported Mathlib, which is not installed in this repository's Lean CI environment; the main source also still contains Mathlib-only tactics. The proof needs a core-Lean port (or a deliberately installed compatible Mathlib dependency) before it can be cited as formal. The earlier `agent10-ray-odd-strip` run failed before reaching this module in the pre-existing `RayIndexHensel` source, so it is not evidence for or against this module.

## 3. Exact 887-family calculation

For `s=5, j=6`, direct exact-integer evaluation of the recursive digit rule gives:

| k | selected h mod 3^k |
|---:|---:|
| 0 | 0 |
| 1 | 0 |
| 2 | 3 |
| 3 | 12 |
| 4 | 66 |
| 5 | 66 |
| 6 | 309 |

For `n = 887 + 13122*T`, write `n=5+6h`. Then
`h = 147 + 2187*T`, so `h mod 81 = 66` but `h mod 243 = 147`. The selector values above therefore predict:
- `3^5 | T_6(n)`, so the second t=1 gate holds;
- `3^6 ∤ T_6(n)`, so `v_3(T_6(n))=5` exactly;
- equivalently, for the actual even parent w, `v_3(2*w+5)=3` exactly.

For n=887, the corresponding residues are `n mod 27 = 23`, `2^n mod 27 = 5`, `d mod 27 = 21`, `q mod 27 = 21`, and `w mod 27 = 11`. In particular `2*w+5 = 0 mod 27`. The previously proposed quotient-parent surrogate has residue 17 mod 27 and is not this w.

The residue calculation is computational evidence pending formal Lean evaluation; the general Hensel theorem is intended to make the full residue statement exact once CI passes.

## 4. What this does and does not close

This identifies the second exceptional gate as a single 3-adic index class at every precision, and gives its exact valuation on the 887 mod 13122 family. It does **not** close the resulting inverse branch. Exact valuation 3 leaves t=0,1,2 to test for w; the source band inequalities must still eliminate impossible exponents, and the surviving t=1 predecessor must be followed through its own even/odd parents. In particular, no conclusion about blank-root reachability or halting follows from this selector alone.

Next: validate the Lean module, then use the exact `v_3(2*w+5)=3` result to perform the t=2 band-gap exclusion for the actual w and continue the genuine ResetParent chain.


## 5. Exact reverse-cone experiment for the remaining evenPre branch

An independent exact BigInt enumeration was run from
`evenPre 887 (887+4) = 4*2^887 - 3*887 - 7`, using the same ResetParent equations as `ParentsFast`:

- even parent: `6*2^k-1 ≤ u ≤ 8*2^k-3`, parent `2*u-8*2^k-k`;
- odd parent: `d=(2*u+5)/3^(t+1)` odd, `6*2^k+1 ≤ 2^t*d ≤ 8*2^k-1`, parent `2^(t+1)*d-8*2^k-k-5`.

For each even parent the unique candidate scale is `k=bitlen(u)-3`; for odd parents every exact 3-adic exponent was enumerated with the same unique-scale rule. The resulting reverse cone has:

- 1,319 distinct states and 1,318 edges (a tree, no merging);
- 181 leaves and maximum depth 876;
- no occurrence of state 2;
- a 877-node main even-ray chain and 162 odd-parent edges;
- every off-chain odd-parent subtree has at most 15 nodes and depth at most 10.

This is computational evidence, **not yet a Lean certificate**. It complements Agent 44's formal exclusion of the oddPre branch. A finite `ParentsFast`/`ClosedCertFast` certificate for this n=887 evenPre cone would close the remaining n=887 instance, but it would not establish the full n ≡ 887 mod 13122 family. The cone grows with n; a uniform classification of the bounded off-chain subtrees is still needed. Details were sent to Agent 44 in `communications/agent44/20261113T005521327Z_agent10-evenpre887-cone-enumeration.md`.

## 6. Current limits and next work

- Do not promote this file or the Hensel module to `results/`: neither is a certified root-exclusion theorem.
- First priority: either port `RayTwoTierIndexHensel.lean` to core Lean tactics and get the dedicated workflow green, or park it and formalize the n=887 evenPre cone with `ParentsFast` and `ClosedCertFast`.
- For the broader family, use the observed bounded side-subtree sizes and the 3-adic depth/index selectors to seek a finite residue-class classification; the n=887 finite cone alone is not uniform in n.
- No conclusion about BB(6), blank-root reachability for the full #746 family, or halting follows from these intermediate results.

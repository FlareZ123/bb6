# Integer carry transducer for the #623 root gap

**Status:** intermediate computational/structural result. This is not an all-time nonhalting proof and does not belong in `results/`.

## Purpose

The existing #623 gap cocycle is naturally expressed in `(z,q)`, but the right branch contains a half coefficient in `q'`. Replacing (q) by (y=6q) gives integer affine maps and exposes a finite ternary carry transducer. This is intended as infrastructure for the buffered middle-digit approach.

The root replay starts at (D(0,7)) and uses the source-shaped evaluator/drain implementation included in [replay.js](./replay.js). The underlying source derivations are in:

- [RootRayGapCocycle.md](../agent1-machine623-3euclidean-correction-bounds/RootRayGapCocycle.md)
- [Agent 3 exact p/q cocycle message](../../communications/agent41/20261118T115445Z_agent1-623-terminal-residue-cocycle.md)
- [Agent 8 source-shaped root replay](../agent8-623-inverse/root_mass_corridor_survey.js)

## Integer coordinates

Put
[
x=z=2g-gamma_s,qquad y=6q,
]
where (g=p-3q), (p=|a-d|), (q=min(a,d)), and (sin{LO,LE,RO,RE}).

The exact maps are
[
L:quad (x',y')=(x-3y+C_L, 3y+F_L),
]
[
R:quad (x',y')=(-4x-3y+C_R, 3x+3y+F_R).
]
The matrices have determinants (3) and (-3), respectively.

Using the convention in which (r) excludes the initial RE evaluator, the correction terms are:

| sector | (C_L) | (F_L) | (C_R) | (F_R) |
|---|---:|---:|---:|---:|
| LO | (-18D-16r-122) | (12D+12r+84) | (12D+4r-6) | (24-6D) |
| LE | (-18D-16r-68) | (12D+12r+48) | (12D+4r-12) | (18-6D) |
| RO | (-18D-16r) | (12D+12r) | (12D+4r-44) | (30-6D) |
| RE | (-18D-16r-52) | (12D+12r+30) | (12D+4r-16) | (18-6D) |

Here (D) is the signed valuation cost and (r) is the drain length. The source bounds used are
[
|D|le ell+1,qquad 0le rle ell.
]
They imply the uniform correction bound
[
|C_L|,|F_L|,|C_R|,|F_R|le B_c:=34ell+140.
]

The predecessor terminal-strip width is (B_t:=4(9ell+22)=36ell+88). Choose
[
B=max(B_c,B_t),qquad
k=min{i:3^i>B},qquad
j=min{i:3^i>B^3}.
]
Then (jge3k-2), so the buffered middle block ([k+2,j-2)) has length at least (2k-6). Also (B<3^k), so the corrections are absorbed into bounded carries before the middle block begins.

## Finite carry transducer

Write (x_i,y_iin{0,1,2}) for ternary digits and (a_i,b_i) for Euclidean quotient carries. For (ige1):

- L:
  [
  x'_iequiv x_i-y_{i-1}+a_ipmod3,qquad
  y'_iequiv y_{i-1}+b_ipmod3.
  ]
- R:
  [
  x'_iequiv-x_i-x_{i-1}-y_{i-1}+a_ipmod3,qquad
  y'_iequiv x_{i-1}+y_{i-1}+b_ipmod3.
  ]

The next carries are the corresponding quotients by 3. The low linear part contributes carries in ([-1,0]), ({0}), ([-3,0]), and ([0,1]) for (L-x), (L-y), (R-x), and (R-y), respectively. Since each low correction has magnitude below (3^k), it contributes an additional carry in ({-1,0,1}). Therefore the following deliberately generous initial carry ranges are safe and are the ones checked by the script:

- L: (a_kin[-2,2]), (b_kin[-2,2]);
- R: (a_kin[-4,1]), (b_kin[-2,2]).

These ranges are invariant under the digit recurrences. The two discarded positions account for the one-place shifts.

## Source-fidelity correction (2026-11-19)

The original committed `replay.js` had an incorrect zero-digit evaluator branch. The pinned Lean definition in [Parity623.lean](../agent49-parity623/Parity623.lean) returns `(a-1, k/3, m+2)` when `a>0` and `k % 3 = 0). Only the `k % 3 = 1` recursive branch updates `m` by `2*(k/3)+3`. The old JavaScript used the recursive-branch update in the zero-digit branch, so it disagreed with the source at the blank root. The replay has been corrected; its four-state prefix assertion now matches `D(6,14), D(6,31), D(26,26), D(2,83)`. The independent [Agent49 C++ evaluator](../agent49-parity623/root_gap_scan.cpp) already used the immediate `m+2` return.

## Reproducible finite observation

Run:

```sh
node replay.js
```

The script checks the exact root source map through 10,000 transitions. The corrected logic was independently replayed in the available JavaScript runtime; the first four source anchors pass. For each state from index 33 onward, it tests both branch transducers and every carry pair in the ranges above. It checks that the resulting (x)-block on ([k+2,j-2)) is neither all 0 nor all 2.

Observed result:

- 9,968 root states checked (indices 33 through 10,000) in a corrected BigInt replay;
- 55 branch/carry cases per state, 548,240 cases total;
- no monochromatic output block;
- block lengths between 7 and 16.

This is stronger than checking only the actual branch and actual correction carry on the finite prefix. It is nevertheless finite computational evidence only.

## Exact source-output cross-check

As a separate finite consistency check, the transducer was compared with the actual next state of the corrected source-shaped map for indices 33 through 2,000 (1,968 transitions). Let (M=3^k), (M_-=3^{k-1}), (x_0=x\bmod M), (x_1=x\bmod M_-), and (y_1=y\bmod M_-). After computing the exact correction terms (C,F) from the source next state, the initial carries are:

- L: (c_x=\lfloor(x_0-3y_1+C)/M\rfloor), (c_y=\lfloor(3y_1+F)/M\rfloor).
- R: (c_x=\lfloor(-x_0-3x_1-3y_1+C)/M\rfloor), (c_y=\lfloor(3x_1+3y_1+F)/M\rfloor).

The (k-1) truncation on shifted terms is essential: the digit at position (k-1) is consumed by the transducer at output position (k), not in the carry below (k). With this split, all 1,968 actual carry pairs lie inside the advertised 55-case rectangles, and every transducer output digit in positions (k+2,\ldots,j-3) agrees exactly with the corresponding digit of the actual next state's (x',y'). There were zero (x)-digit or (y)-digit mismatches.

This is a finite source-consistency check, not an induction over all canonical states. The universal 55-carry test remains the stronger finite statement recorded above; the missing theorem is still closure of the blank-root history condition for all time.

## What this does not prove

The universal-safety predicate has not been shown to be inductive over all canonical states. Arbitrary canonical states can fail to preserve it, so the root-history restriction is essential. The finite observation does not establish that all future root blocks remain safe.

The next mathematical task is to find a finite regular summary of the root blocks (or a stronger root-specific invariant) that is closed under the actual source transition, then formalize the carry bounds and closure argument. No claim about BB(6) or the eventual behavior of the #623 root follows from this note alone.

# TM63 24-cycle source coverage after the current M1-even bridge

**Status:** intermediate proof-graph audit, 17 November 2026. This is not a compiled theorem, a halt proof, or a BB(6) result. It updates the 14 November coverage table against the current exported source signatures.

## 1. Exact 24-cycle

The published root index is
`tm63Index1 = 31 * 2^A - 1`, and the root arithmetic proves
`tm63Index1 = 8*K + 7` with
`K = tm63RootMiddleK` odd. After the first seven middle decrements the
actual source configuration has marker 1 and index `8*K`.

For one increment, the index changes `n -> n-1` and the marker changes
`m -> nextMarker m = (m+2) % 3`. Thus the 24-cycle, starting at the
root-connected boundary `(n mod 8,m)=(0,1)`, is the rotation

| offset | (n mod 8, marker) | current source theorem |
|---:|:---:|---|
| 0 | (0,1) | `m1EvenValuation_counted_increment_source` |
| 1 | (7,0) | `m0Odd_counted_increment_source` |
| 2 | (6,2) | `m2EvenSix_generic_counted_increment_source` |
| 3 | (5,1) | `m1EvenValuation_counted_increment_source` |
| 4 | (4,0) | `m0Even_residue4_counted_increment_source` |
| 5 | (3,2) | `m2Odd_counted_increment_source` |
| 6 | (2,1) | `m1EvenValuation_counted_increment_source` |
| 7 | (1,0) | `m0Odd_counted_increment_source` |
| 8 | (0,2) | **M2 residue-zero all-q source is missing** |
| 9 | (7,1) | `m1EvenValuation_counted_increment_source` |
| 10 | (6,0) | `m0EvenSix_counted_increment_source` |
| 11 | (5,2) | `m2Odd_counted_increment_source` |
| 12 | (4,1) | `m1EvenValuation_counted_increment_source` |
| 13 | (3,0) | `m0Odd_counted_increment_source` |
| 14 | (2,2) | `m2Even_residue2_counted_increment_source` |
| 15 | (1,1) | `m1EvenValuation_counted_increment_source` |
| 16 | (0,0) | **M0 residue-zero all-q source is missing** |
| 17 | (7,2) | `m2Odd_counted_increment_source` |
| 18 | (6,1) | `m1EvenValuation_counted_increment_source` |
| 19 | (5,0) | `m0Odd_counted_increment_source` |
| 20 | (4,2) | `m2Even_residue4_counted_increment_source` |
| 21 | (3,1) | `m1EvenValuation_counted_increment_source` |
| 22 | (2,0) | `m0Even_residue2_counted_increment_source` |
| 23 | (1,2) | `m2Odd_counted_increment_source` |

The same 24 pairs are obtained from the initial `(7,2)` boundary by
rotating the list seven places; this is the sequence already recorded in
the 14 November coordination message. The period is
`lcm(8,3)=24`.

## 2. What the current source signatures actually cover

The current source-level coverage reduces to these nine families:

- **Marker 1, all indices:** `Agent48M1EvenValuationCountedSource.m1EvenValuation_counted_increment_source` in `M1EvenValuationSource.lean`. Its hypotheses are only `0<n`, `n<2^L`, and `0<a`; it factors arbitrary n as `(2*q+1)*2^v`. It covers all eight marker-1 residue classes, including odd n and every 2-adic valuation.
- **Marker 0, all odd indices:** `Agent48M0OddGenericSource.m0Odd_counted_increment_source` in `M0OddGenericSource.lean`.
- **Marker 2, all odd indices:** `Agent42M2OddGeneric.m2Odd_counted_increment_source` in `M2OddGenericStage.lean`.
- **Marker 0, residues 2, 4, 6 mod 8:** `m0Even_residue2_counted_increment_source`, `m0Even_residue4_counted_increment_source`, and `m0EvenSix_counted_increment_source`.
- **Marker 2, residues 2, 4, 6 mod 8:** `m2Even_residue2_counted_increment_source`, `m2Even_residue4_counted_increment_source`, and `m2EvenSix_generic_counted_increment_source`.

The nonzero-residue source wrappers above accept their quotient parameter q=0 (they require only the width bound and exponent positivity), so the final small indices k=2,4,6 are included; the all-odd M0/M2 sources also cover k=1,3,5,7. No separate small-index base theorem is needed for the one-step dispatcher.\n\nThe two remaining branches are both residue zero:

1. **(0,0), marker 0:** `M0EvenEightGenericSource.m0EvenEight_counted_increment_source` currently requires `q % 2 = 1` for `n=8*q`. It therefore covers only `v2(n)=3`, not all positive multiples of eight. The all-q extension is still an experimental proof plan in `M0EvenEightValuationExtension.md`, with candidate helper files `M0EvenEightValuationEncoding.lean`, `M0EvenEightValuationSuffix.lean`, and `M0EvenEightValuationMacros.lean`; there is not yet a complete all-q counted source theorem.
2. **(0,2), marker 2:** there is no complete all-q counted source theorem for `n=8*q`. `M2EvenResidueSixteen.m2Even_residue16_counted_increment_source` covers only `n=32*k+16`, equivalently `q=4*k+2` with `v2(q)=1`; it is a strict subfamily. The broader candidate is `M2EvenResidueZero.md`. The reusable original-machine `12*t+4) H-run is now formalized in `CountedLBinDecHRun.lean`; `M2EvenResidueZeroFrames.lean` composes its 44-step setup, H-run, and 14-step postlude under explicit source-window/H-run premises, and `M2EvenResidueZeroSource.lean` proves the initial `9*a+6) sweep plus setup. The missing piece is the source-side factorization/premises and final E-scan + q4 suffix + counted-drain composition into a full `m2EvenResidueZero_counted_increment_source`.

Accordingly, **22 of the 24 classes have a general counted source theorem; the two unresolved classes are exactly (0,0) and (0,2)**. The all-n M1 theorem is a substantive reduction from the old 14 November table: all eight M1 branches are now covered by one theorem.

## 3. Why both residue-zero rows must be generalized

Write `K=tm63RootMiddleK`, which is odd. The root-connected 24-cycle begins at marker 1, n=8K. In cycle number `j` (zero-based), the two residue-zero rows are:

- marker 2 at offset 8:
  `n = 8*(K - 1 - 3*j)`, so `q₂(j)=K-1-3*j`;
- marker 0 at offset 16:
  `n = 8*(K - 2 - 3*j)`, so `q₀(j)=K-2-3*j`.

Since K is odd, `q₂(j)` is even for even j and odd for odd j; `q₀(j)` is odd for even j and even for odd j. The even quotients can have varying 2-adic valuation as j varies. Thus:

- the existing q-odd M0-even-8q theorem covers the marker-0 residue-zero row in every even-numbered cycle, but not the odd-numbered cycles;
- the M2 n=32k+16 theorem covers only the `v2(q₂)=1` subcase, not all even-numbered cycles, and there is no complete M2 q-odd source theorem either.

This is not a one-off first-cycle gap. The two all-q residue-zero source families are required for the repeated countdown.

## 4. Exact arithmetic obligations for the dispatcher

The existing `SectionResultRunSource.sectionResult_run_of_source_macro` already proves the full primitive-recursive `sectionResult` run by induction, provided a total one-step dispatcher `hmacro` is supplied for every `0<k<2^L`, marker `m`, exponent `a>0`, right counter `b`, and head.

A dispatcher can split on `m % 3` and `k % 8` and call the 22 covered families above plus the two all-q residue-zero theorems. No manual enumeration of the countdown is then needed.

For a residue-zero branch write `k=8*q`. Since the macro premise gives `k>0`, q is positive. From `k<2^L` and `L≥4), obtain `8*q<2^L`. If the all-q source statement is parameterized by `t=v2(q)` and requires `L≥4+t), factor q using `exists_odd_factor_bounded (L-3) q`; this gives `L = ell+4+t` directly. Equivalently, q≥2^t and `2^(t+3)≤8*q<2^L`.

The remaining dispatcher side conditions are routine but must be stated:
- `a>0` is preserved by `nextExponent`: the next exponent is `a+b+1` for marker 0 and `a+b+2` for markers 1 and 2;
- the index bound is preserved because each source step changes k to k-1;
- `nextMarker` is exactly 2, 0, 1 for markers 0, 1, 2 respectively;
- q=0 cannot occur in a residue-zero branch because the dispatcher is called only with k>0.

The root arithmetic already supplies `tm63Index1=8*K+7`, `K) odd, and `tm63Index1<2^L`; see `TM63RootCountdownArithmetic.lean`. Thus every intermediate root index stays below the fixed width. The root-specific positivity of the exponent is also monotone under `nextExponent`.

## 5. Recommended ownership / next proof steps

- Complete **M0 (0,0)** by finishing the already-owned all-q extension. Its target cost is `resetPrefixCost 0 (8*q) a b = 99+12*a+12*v2(q)+3*b`.
- Complete **M2 (0,2)** by finishing the existing source/H-run composition, not by creating another finite simulator. The candidate target cost is `resetPrefixCost 2 (8*q) a b = 107+12*a+12*v2(q)+3*b`.
- Then write one small total dispatcher over `m%3` and `k%8`, and apply `sectionResult_run_of_source_macro` to the authentic root parameters.

**Validation boundary:** all statements above are based on current source signatures and proof drafts. This audit did not compile the new M1 module, the M0 all-q helper files, the M2 residue-zero composition, or the full dispatcher, and it does not certify their transitive axiom profiles. Do not mark a class fully accepted until the exact original-import Lean closure compiles and its exported theorem is checked for `sorryAx`.

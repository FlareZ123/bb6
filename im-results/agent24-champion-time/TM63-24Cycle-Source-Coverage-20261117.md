# TM63 24-cycle source coverage after the M1 all-index bridge

**Status — 17 November 2026.** This is an intermediate proof-graph audit, not a compiled theorem, halt proof, or BB(6) result. It updates the 14 November coverage table against the current exported source signatures.

## 1. Exact 24-cycle

The published root index is `tm63Index1 = 31*2^A - 1`. Root arithmetic proves `tm63Index1 = 8*K+7`, where `K=tm63RootMiddleK` is odd. After the first seven middle decrements, the authentic source configuration has marker 1 and index `8*K`.

One increment changes `n` to `n-1` and marker `m` to `nextMarker m = (m+2)%3`. Starting at the root-connected boundary `(n%8,marker)=(0,1)`, the 24-cycle is:

| Offset | `(n%8, marker)` | Current source theorem |
|---:|:---:|---|
| 0 | (0,1) | `m1EvenValuation_counted_increment_source` |
| 1 | (7,0) | `m0Odd_counted_increment_source` |
| 2 | (6,2) | `m2EvenSix_generic_counted_increment_source` |
| 3 | (5,1) | `m1EvenValuation_counted_increment_source` |
| 4 | (4,0) | `m0Even_residue4_counted_increment_source` |
| 5 | (3,2) | `m2Odd_counted_increment_source` |
| 6 | (2,1) | `m1EvenValuation_counted_increment_source` |
| 7 | (1,0) | `m0Odd_counted_increment_source` |
| 8 | (0,2) | **M2 residue-zero all-q source missing** |
| 9 | (7,1) | `m1EvenValuation_counted_increment_source` |
| 10 | (6,0) | `m0EvenSix_counted_increment_source` |
| 11 | (5,2) | `m2Odd_counted_increment_source` |
| 12 | (4,1) | `m1EvenValuation_counted_increment_source` |
| 13 | (3,0) | `m0Odd_counted_increment_source` |
| 14 | (2,2) | `m2Even_residue2_counted_increment_source` |
| 15 | (1,1) | `m1EvenValuation_counted_increment_source` |
| 16 | (0,0) | **M0 residue-zero all-q source missing** |
| 17 | (7,2) | `m2Odd_counted_increment_source` |
| 18 | (6,1) | `m1EvenValuation_counted_increment_source` |
| 19 | (5,0) | `m0Odd_counted_increment_source` |
| 20 | (4,2) | `m2Even_residue4_counted_increment_source` |
| 21 | (3,1) | `m1EvenValuation_counted_increment_source` |
| 22 | (2,0) | `m0Even_residue2_counted_increment_source` |
| 23 | (1,2) | `m2Odd_counted_increment_source` |

The same 24 pairs are obtained by rotating the previously recorded `(7,2)` boundary by seven places. The period is `lcm(8,3)=24`.

## 2. What the current source signatures cover

The current source-level coverage reduces to nine families:

- **Marker 1, all indices:** `Agent48M1EvenValuationCountedSource.m1EvenValuation_counted_increment_source` in `M1EvenValuationSource.lean`. Its hypotheses are only `0<n`, `n<2^L`, and `0<a`; it factors arbitrary n as `(2*q+1)*2^v`. It covers all eight marker-1 residues and every 2-adic valuation. The theorem is written and manually reviewed, but not yet compiled.
- **Marker 0, all odd indices:** `Agent48M0OddGenericSource.m0Odd_counted_increment_source` in `M0OddGenericSource.lean`.
- **Marker 2, all odd indices:** `Agent42M2OddGeneric.m2Odd_counted_increment_source` in `M2OddGenericStage.lean`.
- **Marker 0, residues 2, 4, 6 mod 8:** `m0Even_residue2_counted_increment_source`, `m0Even_residue4_counted_increment_source`, and `m0EvenSix_counted_increment_source`.
- **Marker 2, residues 2, 4, 6 mod 8:** `m2Even_residue2_counted_increment_source`, `m2Even_residue4_counted_increment_source`, and `m2EvenSix_generic_counted_increment_source`.

The nonzero-residue even wrappers accept quotient parameter q=0 (they require only their width bound and exponent positivity), so k=2,4,6 are included. The odd wrappers cover k=1,3,5,7. No separate small-index base theorem is needed for the one-step dispatcher.

The two remaining branches are both residue zero:

1. **(0,0), marker 0:** `M0EvenEightGenericSource.m0EvenEight_counted_increment_source` currently requires `q%2=1` for `n=8*q`; it therefore covers only `v₂(n)=3`. The all-q extension plan and helper modules are in `M0EvenEightValuationExtension.md`, `M0EvenEightValuationEncoding.lean`, `M0EvenEightValuationSuffix.lean`, and `M0EvenEightValuationMacros.lean`. There is not yet a complete all-q counted source theorem.
2. **(0,2), marker 2:** there is no complete all-q counted source theorem for `n=8*q`. `M2EvenResidueSixteen.m2Even_residue16_counted_increment_source` covers only `n=32*k+16`, equivalently `q=4*k+2` with `v₂(q)=1`. The broader source integration is documented in [M2EvenResidueZero-SourceIntegration-20261117.md](M2EvenResidueZero-SourceIntegration-20261117.md). It now has an exact factorization, source-side H-run input-word derivation, q4 cut word, right-shape/cost calculation, and uncompiled generic H-run left-facing/right-boundary lemma candidates. The complete all-q counted source theorem is still missing.

Accordingly, **22 of the 24 classes have current general counted-source theorem declarations**; the two unresolved classes are exactly `(0,0)` and `(0,2)`. The all-index M1 theorem is a substantive reduction from the older table: all eight marker-1 branches are covered by one theorem.

## 3. Why both residue-zero rows must be generalized

Write `K=tm63RootMiddleK`, which is odd. The root-connected 24-cycle begins at marker 1, n=8K. In cycle number j (zero-based), the two residue-zero rows are:

- Marker 2 at offset 8: `n=8*(K-1-3*j)`, so `q₂(j)=K-1-3*j`.
- Marker 0 at offset 16: `n=8*(K-2-3*j)`, so `q₀(j)=K-2-3*j`.

Since K is odd, `q₂(j)` is even for even j and odd for odd j; `q₀(j)` is odd for even j and even for odd j. The even quotients can have varying 2-adic valuation. Thus the existing q-odd M0 theorem covers the marker-0 residue-zero row only on even-numbered cycles, and the M2 `n=32*k+16` theorem covers only the `v₂(q₂)=1` subfamily. These are repeated countdown obligations, not a one-off first-cycle gap.

## 4. Conditional total dispatcher

The existing `SectionResultRunSource.sectionResult_run_of_source_macro` proves the full primitive-recursive `sectionResult` run by induction once a total one-step dispatcher `hmacro` is supplied for every `0<k<2^L`, marker m, exponent `a>0`, right counter b, and head.

`TM63SourceIncrementDispatcher.lean` now contains an uncompiled integration candidate:

- `tm63_source_increment_dispatch` splits on `m%3` and `k%8`, dispatches the 22 covered classes, and leaves exactly two hypotheses for the all-q marker-0 and marker-2 residue-zero sources.
- `sectionResult_run_of_two_zero_sources` applies the existing `sectionResult_run_of_source_macro` theorem to obtain the complete `sectionResult` run under those two hypotheses.

The normalized zero-row hypotheses require `q>0`, `4≤L`, `8*q<2^L`, and `a>0`, with the exact original-machine counted-increment endpoints. The dispatcher source names, argument order, bounds, and target markers/exponents were manually cross-checked against the 22 imported declarations. The file has not been compiled.

For a residue-zero branch, `k=8*q` and the macro premise `k>0` gives q>0. If the M0 all-q proof is parameterized by `t=v₂(q)` and requires `L≥4+t`, factor q using `exists_odd_factor_bounded (L-3) q`; this gives `L=ell+4+t`. The other dispatcher side conditions are routine: `a>0` is preserved by `nextExponent`, k decreases by one, and `nextMarker` is 2, 0, 1 for markers 0, 1, 2 respectively.

The root arithmetic supplies `tm63Index1=8*K+7`, K odd, and `tm63Index1<2^L`; see `TM63RootCountdownArithmetic.lean`. The section countdown therefore remains within the fixed width.

## 5. Exact next steps and validation boundary

1. Complete **M0 (0,0)** by finishing the all-q extension. Its target reset-prefix cost is `99+12*a+12*v₂(q)+3*b`, from `resetPrefixCost 0 (8*q) a b`.
2. Complete **M2 (0,2)** by formalizing the source/H-run composition in the linked integration note. Its target reset-prefix cost is `107+12*a+12*v₂(q)+3*b`, from `resetPrefixCost 2 (8*q) a b`.
3. Compile the exact original-import closure for both zero-row sources, then compile and axiom-audit `TM63SourceIncrementDispatcher.lean`.
4. Apply the resulting `sectionResult` theorem at the authentic root parameters and connect its endpoint to the remaining terminal source itinerary.

**Validation boundary:** this audit is based on current source signatures, mathematical derivations, and uncompiled proof drafts. It does not certify a combined dependency closure or transitive axiom profile. Do not mark a class accepted until the exact original-import Lean closure compiles and the exported theorem is checked for `sorryAx`. No CI run is claimed for the new dispatcher or H-run drafts.

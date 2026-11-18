# TM63 24-cycle source coverage: both residue-zero rows drafted

**Status — 18 November 2026.** This is an intermediate proof-graph audit, not a compiled 24-cycle theorem, halt proof, or BB(6) result. The marker-2 and marker-0 residue-zero counted-source compositions now both have full source drafts; neither has passed exact import-closure compilation or a transitive axiom audit.

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
| 8 | (0,2) | `m2Even_residue0_counted_increment_source` (full all-q draft; uncompiled) |
| 9 | (7,1) | `m1EvenValuation_counted_increment_source` |
| 10 | (6,0) | `m0EvenSix_counted_increment_source` |
| 11 | (5,2) | `m2Odd_counted_increment_source` |
| 12 | (4,1) | `m1EvenValuation_counted_increment_source` |
| 13 | (3,0) | `m0Odd_counted_increment_source` |
| 14 | (2,2) | `m2Even_residue2_counted_increment_source` |
| 15 | (1,1) | `m1EvenValuation_counted_increment_source` |
| 16 | (0,0) | `m0EvenEight_valuation_counted_increment_source` (full all-q source draft; uncompiled) |
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

The two residue-zero rows now both have complete source-level counted compositions:

1. **(0,0), marker 0 — full all-q source draft.** `M0EvenEightValuationQ4Source.lean` exports `m0EvenEight_valuation_q4_prefix_leftFacing`, `m0EvenEight_valuation_q4_prefix_rightShape`, `m0EvenEight_valuation_q4_prefix_far_tail`, and `m0EvenEight_valuation_q4_reset_prefix_source`. `M0EvenEightValuationCountedSource.lean` composes the generic counted drain and exports `m0EvenEight_valuation_counted_increment_source` for every `q>0`, with `4≤L`, `8*q<2^L`, and `a>0`. The prefix cost is `60+12*a+12*v₂(q)`; the reset-prefix cost is `99+12*a+12*v₂(q)+3*b`. The proof uses the existing valuation helpers in [M0EvenEightValuationSource.lean](../agent48-counted-inc0/M0EvenEightValuationSource.lean), [M0EvenEightValuationSuffix.lean](../agent48-counted-inc0/M0EvenEightValuationSuffix.lean), and [M0EvenEightValuationEncoding.lean](../agent48-counted-inc0/M0EvenEightValuationEncoding.lean). Agent 42 corrected the false markerWord(2)-length objection; Agent 4's [independent symbolic coordinate review](../../communications/agent48/20261118T121242Z_agent4-m0-valuation-coordinate-review.md) checks the scan-block partition and exit boundary for arbitrary t. The source chain and its final counted theorem remain uncompiled and unaudited.
2. **(0,2), marker 2 — full all-q source draft.** `M2EvenResidueZeroCounted.lean` exports `m2Even_residue0_q4_reset_prefix_source` and `m2Even_residue0_counted_increment_source` for `n=8*q`, `q>0`, with target prefix cost `107+12*a+12*v₂(q)+3*b`. It composes the source-side H-run, q4 suffix and counted drain. Direct dependencies include `M2EvenResidueZeroSource`, `LBinDecHRunLeftFacing`, `Q4RightEndpoint`, and `S1CountedDrain`. The target file contains no explicit `sorry`, `axiom`, or `native_decide`, and has `#print axioms` declarations, but the exact import closure has not yet been compiled and the transitive axiom profiles have not been inspected. The existing manual workflow [agent8-m2-even-residue-zero-finite.yml](../../.github/workflows/agent8-m2-even-residue-zero-finite.yml) stages this counted module and its source dependencies; it must not be dispatched until local exact-source preflight succeeds.

Accordingly, **24 of the 24 24-cycle classes now have a counted-source theorem declaration or full source draft**. This is source-draft coverage only: neither residue-zero counted composition has passed the exact original-import compile and transitive axiom audit, and the full dispatcher/root itinerary is not yet compiler-certified.

## 3. Why both residue-zero rows must be generalized

Write `K=tm63RootMiddleK`, which is odd. The root-connected 24-cycle begins at marker 1, n=8K. In cycle number j (zero-based), the two residue-zero rows are:

- Marker 2 at offset 8: `n=8*(K-1-3*j)`, so `q₂(j)=K-1-3*j`.
- Marker 0 at offset 16: `n=8*(K-2-3*j)`, so `q₀(j)=K-2-3*j`.

Since K is odd, `q₂(j)` is even for even j and odd for odd j; `q₀(j)` is odd for even j and even for odd j. The new M2 all-q draft covers every positive `q₂(j)` at source-draft level, pending exact compilation. The M0 all-q draft now covers every positive `q₀(j)` at source-draft level as well. Therefore the 24-cycle has complete source-draft coverage for every positive quotient; the remaining gap is validation and root composition, not another residue class.

## 4. Conditional total dispatcher

The existing `SectionResultRunSource.sectionResult_run_of_source_macro` proves the full primitive-recursive `sectionResult` run by induction once a total one-step dispatcher `hmacro` is supplied for every `0<k<2^L`, marker m, exponent `a>0`, right counter b, and head.

`TM63SourceIncrementDispatcher.lean` retains the uncompiled two-hypothesis dispatcher:

- `tm63_source_increment_dispatch` splits on `m%3` and `k%8`, dispatching the 22 previously covered classes and leaving the all-q marker-0 and marker-2 residue-zero sources.
- `sectionResult_run_of_two_zero_sources` applies `sectionResult_run_of_source_macro` under those two hypotheses.

The new `TM63SourceIncrementDispatcherM2.lean` is a second uncompiled integration layer. It supplies the marker-2 hypothesis from `M2EvenResidueZeroCounted.m2Even_residue0_counted_increment_source` and exports `tm63_source_increment_dispatch_m2` plus `sectionResult_run_of_m0_zero_source`. Thus the full `sectionResult` run is now conditional only on validating and instantiating the matching marker-0 all-q source draft; both residue-zero source dependencies remain uncompiled. This wrapper inherits the uncompiled M2 dependency and is not compiler-certified. The new `TM63SourceIncrementDispatcherComplete.lean` imports this M2 wrapper and the M0 all-q counted source, supplies the remaining marker-0 hypothesis, and exports `tm63_source_increment_dispatch_complete`, `sectionResult_run_to_index_one_complete` (leaving index one for the final reset prefix), and `sectionResult_run_complete`. This closes the 24-class dispatcher at source-draft level: if its exact dependencies are accepted, it proves the original-TM2 `sectionResult` run for every valid S1 input. The complete wrapper is uncompiled and does not establish the authentic blank-root connection or terminal endpoint.

The normalized zero-row hypotheses require `q>0`, `4≤L`, `8*q<2^L`, and `a>0`, with the exact original-machine counted-increment endpoints. The dispatcher source names, argument order, bounds, and target markers/exponents were manually cross-checked against the imported declarations. None of the three dispatcher files has been compiled.

For a residue-zero branch, `k=8*q` and the macro premise `k>0` gives q>0. If the M0 all-q proof is parameterized by `t=v₂(q)` and requires `L≥4+t`, factor q using `exists_odd_factor_bounded (L-3) q`; this gives `L=ell+4+t`. The other dispatcher side conditions are routine: `a>0` is preserved by `nextExponent`, k decreases by one, and `nextMarker` is 2, 0, 1 for markers 0, 1, 2 respectively.

The root arithmetic supplies `tm63Index1=8*K+7`, K odd, and `tm63Index1<2^L`; see `TM63RootCountdownArithmetic.lean`. The section countdown therefore remains within the fixed width.

## 4a. Root-specific index-one handoff

`TM63RootAfterSectionResultToOne.lean` composes the authentic blank-root theorem through middle 34 with the complete dispatcher, stopping at index one. The arithmetic is: `first_stage_exponent_odd` gives A odd; hence `2^(A-3) = 1 (mod 3)`, `K=31*2^(A-3)-1 = 0 (mod 3)`, and `r=K/2 = 1 (mod 3)`. Middle 34 has `n=16*r-19 = 0 (mod 3)`, `m=1`. Running `n-1` decrements leaves `n=1,m=2`. The file exports the exact blank-root run theorem `tm63_blank_reaches_after_middle34_to_index_one`.

This is a useful root-connected source result, but it is not a halt witness. The m=2,n=1 `resetBase_odd_frame` source currently covers only a=b=0 and does not yet prove exact S0-config equality. The arbitrary-a,b reset prefix and terminal SectionBits join remain open. This root wrapper is uncompiled.

## 5. Exact next steps and validation boundary

1. Run local Lean 4.36.0-rc2 preflight on the exact original import closure of `TM63SourceIncrementDispatcherComplete.lean` using `tools/lean_compile_closure.py`. This closure includes the M0 and M2 residue-zero counted sources and all 22 other one-step families; resolve missing or ambiguous imports explicitly.
2. Inspect the final axiom profiles of `tm63_source_increment_dispatch_complete`, `sectionResult_run_to_index_one_complete`, and `sectionResult_run_complete`; reject `sorryAx`, `native_decide`, and custom axioms. Only after local preflight passes, run the manual `tm63-24cycle-dispatcher` workflow target.
3. Run the exact local import-closure preflight for `TM63RootAfterSectionResultToOne.lean`; audit the four exported root theorem profiles. Only after this preflight passes, run the manual `tm63-root-index-one` workflow target.
4. Generalize the m=2, n=1 reset-base prefix from a=b=0 to arbitrary a,b, prove its exact S0-config/SectionBits embedding, and connect the terminal macro.
5. Continue the independent universal six-state upper-bound programme; a lower-bound witness alone does not determine BB(6).

**Validation boundary:** this audit is based on current source signatures, mathematical derivations, and uncompiled proof drafts, including the new complete dispatcher wrapper. It does not certify a combined dependency closure or transitive axiom profile. Do not mark a class accepted until the exact original-import Lean closure compiles and every exported `#print axioms` profile is inspected; reject `sorryAx`, `native_decide`, and custom axioms. Standard Lean axioms such as `propext`, `Classical.choice`, and `Quot.sound` are expected. No CI run is claimed for the M2 counted draft, the M0 valuation extension, or the dispatcher.

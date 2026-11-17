# TM63 source rows 32–34 and authentic-root middle-34 continuation

**Research state (17 November 2026):** The repository now contains source-level Lean statements for (i) the generic marker-2 even increment at indices (n=8q+6), (ii) the marker-1 even increment for every positive bounded index, and (iii) the authentic blank-root TM63 continuation through middle row 34. The root theorem is now **unconditional at the source level**: it derives row 32 from the all-valuation M1 theorem, then composes rows 33 and 34. The combined dependency closure has **not yet passed Lean compilation or an axiom audit**. Treat all three new/changed modules as drafts until the existing manual acceptance target succeeds.

## Generic marker-2 even row: (n=8q+6)

For (L,q,a,b\in\mathbb N), (h\in\mathbb Z), (3\le L), (8q+6<2^L), and (a>0), M2EvenSixGenericSource.lean proves the original-table reset-prefix run
[
\operatorname{run}\ tm2\ (\operatorname{resetPrefixCost}\ 2\ (8q+6)\ a\ b)\
(s1Config\ L\ (8q+6)\ 2\ a\ 0\ b\ h)
=
\operatorname{some}(s1Config\ L\ (8q+5)\ 1\ (a+b+2)\ (2^b-1)\ 0\ (h+5+3b)).
]
The proof lifts the fixed (L=3,n=6) q4 prefix to arbitrary (q) by a finite-window frame. The source and target encodings have a common tail after the low three blocks; the proof identifies the finite region read by the prefix, preserves the q4 right guard, and proves the far-right blank tail.

M2EvenSixGenericCounted.lean composes that prefix with the existing S1 counted drain. Its exported theorem m2EvenSix_generic_counted_increment_source proves
[
\operatorname{run}\ tm2\ (\operatorname{proposedIncrementCost}\ 2\ (8q+6)\ a\ b)\
(s1Config\ L\ (8q+6)\ 2\ a\ 0\ b\ h)
=
\operatorname{some}(s1Config\ L\ (8q+5)\ 1\ (a+b+2)\ 0\ (2^b-1)\ (h+5+3b)).
]
This is a statement about the repository's original tm2 and infinite-tape run, not a copied transition system.

## Authentic blank-root composition through middle row 34

Let (R=\texttt{tm63RootResidueSixK}). The current root composition starts from the established authentic blank-root endpoint at middle 26 and uses the source increments for rows 27–34. The three decisive later rows are:

| Row | Input marker | Input index | Source theorem |
|---:|---:|---:|---|
| 32 | 1 | (16R-16) | m1EvenValuation_counted_increment_source |
| 33 | 0 | (16R-17) | m0Odd_counted_increment_source |
| 34 | 2 | (16R-18=8(2R-3)+6) | m2EvenSix_generic_counted_increment_source |

For row 32, M1EvenValuationSource.lean factors every positive (n<2^L) as ((2q+1)2^v) and proves the complete counted increment without a valuation side condition. The root arithmetic establishes (0<16R-16<2^{\texttt{tm63Length1}}) and a positive left counter, so the generic theorem applies directly. Row 33 is odd and uses the generic M0 odd theorem. Row 34 is the (n=8q+6) theorem above with (q=2R-3).

TM63RootMiddle34.lean defines the exact accumulated cost tm63MiddleFirst34Moves and proves
[
\operatorname{run}\ tm2\ \texttt{tm63MiddleFirst34Moves}\ \texttt{blank}
=
\operatorname{some}(s1Config\ \texttt{tm63Length1}\ (16R-19)\ 1\
\texttt{tm63MiddleAfter34A}\ 0\ \texttt{tm63MiddleAfter34B}\
\texttt{tm63MiddleAfter34Head}).
]
The main theorem is tm63_blank_reaches_after_middle34; it has no extra row-32 hypothesis. The older theorem tm63_blank_reaches_after_middle34_of_m1even32 remains only as a backwards-compatible wrapper.

This is a genuine source-level root-prefix candidate, not a halt witness. It neither closes the 24-class countdown nor proves the later itinerary, the champion's exact primitive-step count, or any global six-state upper bound.

## Verification and acceptance gate

The existing manual workflow .github/workflows/agent42-champion-terminal-source.yml already has the focused workflow_dispatch target middle34-acceptance. It invokes tools/lean_compile_closure.py on exactly these three roots:

1. im-results/agent48-counted-inc0/M1EvenValuationSource.lean;
2. im-results/agent44-tm63-middle/M2EvenSixGenericCounted.lean;
3. im-results/agent44-tm63-middle/TM63RootMiddle34.lean.

The closure compiler resolves and compiles their transitive project imports under Lean 4.36.0-rc2. The job extracts the three exported #print axioms lines for m1EvenValuation_counted_increment_source, m2EvenSix_generic_counted_increment_source, and tm63_blank_reaches_after_middle34, and rejects sorryAx or native_decide. This focused job is separate from the broad serial terminal-source job, so an unrelated earlier failure does not mask this target. **The focused job has not yet been dispatched or passed**; no source-certification claim is made here.

## Next useful action

Run the existing middle34-acceptance target once on the current main revision, inspect the first compiler error if it fails, or record the three final axiom profiles if it succeeds. Do not add another workflow or widen this acceptance target before it passes. After acceptance, the next root step is marker 1 at index (16R-19=8(2R-3)+5), for which the separate M1OddResidueFive.lean source theorem is available; that next row is not part of the present acceptance claim.

# TM63 source rows 32–37 and authentic-root middle-34 continuation

**Status (2026-11-19):** The repository contains an unconditional source-level blank-root TM63 continuation through middle row 34, a source-level composition from that endpoint through the complete SectionResult dispatcher to index one and the outer-LC_Inc nested reset frame, and a new source-only composition of that frame with the canonical marker-1 S0 endpoint. A separate direct row-by-row extension through row 37 also exists. None of these new root/endpoint chains is accepted by the focused Lean gate yet. The exact primitive-step count of the champion and a universal six-state upper bound remain open.

## Generic source increments and the authentic root

Let \(R=\texttt{tm63RootResidueSixK}\). The maintained root module TM63RootMiddle34.lean composes rows 27–34. Its decisive rows are:

| Row | Input marker | Input index | Source theorem |
|---:|---:|---:|---|
| 32 | 1 | \(16R-16\) | m1EvenValuation_counted_increment_source |
| 33 | 0 | \(16R-17\) | m0Odd_counted_increment_source |
| 34 | 2 | \(16R-18=8(2R-3)+6\) | m2EvenSix_generic_counted_increment_source |

The row-32 theorem factors every positive bounded index into an odd factor times a power of two and discharges the complete counted increment without a valuation side condition. Row 33 is the generic odd marker-0 increment. Row 34 is the all-parameter marker-2 even-six increment.

TM63RootMiddle34.lean defines the exact accumulated cost tm63MiddleFirst34Moves and proves

\[
\operatorname{run}\ tm2\ \texttt{tm63MiddleFirst34Moves}\ \texttt{blank}
=
\operatorname{some}\bigl(s1Config\ \texttt{tm63Length1}\ (16R-19)\ 1\
\texttt{tm63MiddleAfter34A}\ 0\ \texttt{tm63MiddleAfter34B}\
\texttt{tm63MiddleAfter34Head}\bigr).
\]

The main theorem is tm63_blank_reaches_after_middle34; it has no extra row-32 hypothesis. This is a source-level root-prefix statement, not a halt witness.

A separate direct extension, TM63RootMiddle37.lean, appends three more source increments:

| Row | Input marker | Input index | Source theorem |
|---:|---:|---:|---|
| 35 | 1 | \(16R-19=8(2R-3)+5\) | m1ResidueFive_counted_increment_source |
| 36 | 0 | \(16R-20=8(2R-3)+4\) | m0Even_residue4_counted_increment_source |
| 37 | 2 | \(16R-21\), odd | m2Odd_counted_increment_source |

It states tm63_blank_reaches_after_middle37, ending at index \(16R-22\), marker 1. This direct row-35–37 extension is still an uncompiled draft and is not part of the current acceptance target.

## Index-one reset frame and the actual terminal boundary

TM63RootAfterSectionResultToOne.lean takes the middle-34 root state through the complete 24-class SectionResult dispatcher to index one, marker two, then applies outerLCInc_full_run. Its theorem tm63_blank_reaches_after_middle34_reset_frame reaches state 3 with the exact nested outerLCIncPostludeTape. The current manual acceptance target includes this root module and audits its exported theorem profile.

The next pointwise identification is drafted in im-results/agent42-outer-lcinc/OuterLCIncCanonicalEndpoint.lean. For \(n=1,m=2\), the exact source-run cost is \(12a+71+3b\), and the file proves at source level that the nested frame is the canonical marker-1 S1/S0 endpoint:

\[
s1Config\ L\ 0\ 1\ (a+b+2)\ (2^b-1)\ 0\ (h+3b+5),
\]

equivalently the S0 input with left word markerWord 1 ++ d0 ++ d1pow L ++ lh and positive right counter \(z=2^b-1\). The declarations outerLCIncPostludeTape_eq_s1Config_m2 and outerLCIncPostludeTape_eq_marker1S0_m2 are not yet in the acceptance closure and have not been Lean-compiled or axiom-audited.

The new [TM63RootMarker1Endpoint.lean](TM63RootMarker1Endpoint.lean) composes `outerLCIncPostludeTape_eq_marker1S0_m2` with `tm63_blank_reaches_after_middle34_reset_frame`. Its theorem `tm63_blank_reaches_after_middle34_marker1_s0` states the resulting authentic blank-root run directly at the canonical marker-1 S0 input, with width (A=\texttt{middle34Result.exponent}+\texttt{middle34Result.right}+2), right counter (z=2^{\texttt{middle34Result.right}}-1), and the exact final head. It also imports the generic width/value bounds. This integration is **uncompiled source draft**; it does not establish halting or close the positive-(z) q4 macro.

**Additional interface blocker identified during source review (not yet a Lean diagnostic):** `outerLCInc_s1_postlude_run` returns a postlude frame over `outerLCIncSourceT3 T h a m r`, and `outerLCInc_preHRun` reaches that same T3 tape. But the current `outerLCInc_full_run` statement in `OuterLCIncPostludeSource.lean` appears to claim the frame over the original S1 tape `T`. The postlude tape is a finite frame over its input and preserves the far-left cells; T3 has already changed the left-facing source word. The root wrapper currently repeats the original-T output, while the canonical endpoint lemma expects T3. This likely needs correction by carrying the existential `r` and T3 tape through `outerLCInc_full_run` and `TM63RootAfterSectionResultToOne.lean`. The source-level diagnosis was sent to Agents 42 and 48 and is pending their review / exact preflight; do not treat the new root-marker1 wrapper as type-checked.

The current root wrapper has \(L=\texttt{tm63Length1}=76\): tm63FirstSection.exponent is nextExponent 2 6 63 = 71, and tm63Length1 = 3 + 71 + 2. The source lemma tm63Length1_even is in TM63Length1Parity.lean. The authentic endpoint also has \(z=2^b-1\ge3\), so the marker-1 experiments that set \(z=0\) do not directly close the root. In particular, the exact z=0 even-L terminal law is not a positive-z theorem. The positive-z q4 nested-counter macro, its cycle recurrence, and the final halt remain open.

## Focused Lean acceptance

The existing manual-only target middle34-acceptance in .github/workflows/agent42-champion-terminal-source.yml is the acceptance path. It reconstructs the authoritative terminal imports, then compiles the exact dependency closures of these five roots:

1. im-results/agent48-counted-inc0/M1EvenValuationSource.lean
2. im-results/agent44-tm63-middle/M2EvenSixGenericCounted.lean
3. im-results/agent44-tm63-middle/TM63RootMiddle34.lean
4. im-results/agent48-counted-inc0/TM63RootAfterSectionResultToOne.lean
5. im-results/agent48-counted-inc0/Q4S0FirstCycleMacros.lean

It audits 14 exported declarations, including the two generic counted increments, the middle-34 root theorem, the complete SectionResult dispatcher, the index-one marker-two theorem, the reset-base prefix/suffix, the nested-frame root theorem, and outerLCInc_target_binary_prefix. The accepted foundational axiom set is {propext, Classical.choice, Quot.sound}; sorryAx and native_decide are rejected. This is a focused manual job, not a per-commit workflow.

Two current-main dispatches have failed on genuine Lean obligations:

- Run 44424308953 (head f0b7edc…) exposed unresolved tape-extensionality goals in both M1EvenState1Sweep.lean and M1EvenState5Sweep.lean.
- Run 44438791470 (head 95a3438…) compiled the state-5 sweep, but failed in M1EvenState1Sweep.lean at lines 56 and 66. The remaining goals were coordinate-normalization failures: Lean retained h - 1 + (-1) instead of identifying it with h - 2.

Commit 9103e64b22f72afae47f53e8963426ff7db93bc3 adds the explicit identity heq3 : h - 1 + (-1 : Int) = h - 2 to the state-1 extensionality proof and supplies it to the two affected simp calls. This is the direct repair for the two observed goals, but it has **not yet been tested**. No acceptance or axiom-audit claim is made until a new run passes.

## Next proof actions

1. Obtain exact local Lean preflight for the patched current main, including the M1 `heq3` repair and the downstream `OuterLCIncPostludeSource` / root-wrapper chain. Resolve the T3/original-tape interface mismatch before any CI dispatch.
2. Only after that preflight passes, dispatch the existing middle34-acceptance target once. Inspect the first actual Lean diagnostic if it fails; do not repeat previous unpatched runs.
3. If it passes, record all 14 exported axiom profiles and preserve the root-to-nested-frame boundary exactly as proved.
4. Only after that acceptance, add a separate narrow manual acceptance target for TM63RootMiddle37.lean, OuterLCIncCanonicalEndpoint.lean, and TM63RootMarker1Endpoint.lean; do not widen the current target before it passes.
5. Formalize the positive-z q4 checkpoint/first-cycle macro and connect its exact cost and final halt to the authentic L=76, z≥3 endpoint.

All material described here remains in im-results/ until it meets the repository's academically publishable results/ standard. No exact BB(6) value, complete champion halt count, or universal six-state upper bound is established.

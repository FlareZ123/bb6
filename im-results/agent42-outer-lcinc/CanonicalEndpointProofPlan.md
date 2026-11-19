# Canonical endpoint for the outer LC increment run

**Status (2026-11-19):** The exact source-run theorem and a complete pointwise marker-1 canonical-endpoint proof are now present in Lean source. The endpoint file has not yet been compiled or axiom-audited, so this is still intermediate work, not an accepted theorem.

## Exact source run

OuterLCIncPostludeSource.lean exports outerLCInc_full_run. Its run cost is

\[
12a+4m+63+12v_2(n)+3b
\]

and its output is the nested outerLCIncPostludeTape frame in state 3, at head \(h+3b+5\).

For \(n=1,m=2\), the cost is \(12a+71+3b\), and the intended canonical endpoint is

    s1Config L 0 1 (a+b+2) (2^b-1) 0 (h+5+3*b)

which is equivalently the marker-1 S0 input with left word

    s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) (a+b+2) (2^b-1) 0 H

where \(H=h+3b+5\).

## Pointwise proof already drafted

OuterLCIncCanonicalEndpoint.lean now contains the complete source-level chain for the \(m=2,n=1\) case:

1. outerLCIncSourceT3_leftFacing_m2: the zero-valuation H-run and left-facing source stream.
2. outerLCIncAfterZero_leftFacing_m2: the E-scan, five-step marker frame, H-run bridge, and zero boundary.
3. outerLCIncAfterSweep_leftFacing_m2: the B/F/D sweep's \(d0pow\ b\) prefix, split by residues modulo 3.
4. outerLCIncPostludeTape_leftFacing_m2 and outerLCIncPostludeTape_rightFacing_m2: the fixed tail and complete pointwise tape streams.
5. outerLCIncPostludeTape_eq_s1Config_m2: identification with the canonical S1 encoding.
6. outerLCIncPostludeTape_eq_marker1S0_m2: the exact marker-1 S0 interface.
7. outerLCInc_marker1S0_inputBounds: positivity and binary-width bounds for the endpoint parameters.

These declarations replace the five pointwise tasks listed in the earlier version of this plan. They are **source candidates only** until the complete dependency closure compiles and the exported declarations pass an axiom audit.

## Authentic-root composition

TM63RootAfterSectionResultToOne.lean already composes the blank-root middle-34 theorem with the complete 24-class SectionResult dispatcher to index one, marker two, then with outerLCInc_full_run. The resulting theorem tm63_blank_reaches_after_middle34_reset_frame ends at the exact nested frame. It does not yet import or use OuterLCIncCanonicalEndpoint.lean; composing outerLCIncPostludeTape_eq_marker1S0_m2 with this root theorem is the next formal integration step.

The current root wrapper has \(L=\texttt{tm63Length1}=76\), which is even. The authentic marker-1 S0 endpoint has positive right counter \(z=2^b-1\ge3\). The experiments in Marker1TerminalExperiment.md and the exact even-L law in Marker1EvenTerminalMacroConjecture.md use \(z=0\); they do not directly prove the authentic root's positive-z terminal behavior.

## Verification and remaining mathematics

The current manual middle34-acceptance job compiles the five root modules listed in im-results/agent44-tm63-middle/README.md and audits the nested-frame declarations, but does not compile OuterLCIncCanonicalEndpoint.lean. The latest run failed earlier in M1EvenState1Sweep.lean; commit 9103e64 adds the exact coordinate normalization \(h-1+(-1)=h-2\), and a rerun is pending.

After the middle-34 gate passes:

1. Compile the complete dependency closure of OuterLCIncCanonicalEndpoint.lean and audit all exported endpoint declarations.
2. Compose the canonical endpoint equality with tm63_blank_reaches_after_middle34_reset_frame.
3. Prove the positive-z q4 nested-counter macro, including its checkpoint recurrence, exact cycle costs, final terminal frame, and halt query.

The z=0 terminal theorem and the finite positive-z simulations are not substitutes for this proof. No complete champion halting trajectory or exact BB(6) upper bound is established here.

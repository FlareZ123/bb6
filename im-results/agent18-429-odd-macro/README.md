# Shared radix-16 inverse graph for the long odd-reset branch of #429

## Main result

Under the same exact Source interface used in [Q0MacroCore](../agent1-429-q0-23-7/Q0MacroCore.lean), a reachable state (a,b) with a odd, b+3=2a, n>=18 and 4a+3n+15=3*2^(n+2) requires one of these two strict-interior signed paths:

| inverse prefix | n | length m | rank p | height y |
| --- | --- | --- | --- | --- |
| FF | 63+64t | 13+16t | 53+48t | 3+3t |
| FE | 39+64t | 8+16t | 36+48t | 11+15t |

Here t is a nonnegative integer. Both paths use the existing digits 0,1,4,5 and the same rank and height recurrences. The first row combines a mod32=13,29; the second combines 15,31 (31 is already excluded by the branch-7 residue proof). This avoids independent symbolic treatment of three residue families.

[OddResetMacro.lean](OddResetMacro.lean) proves the reduction. In brief, first F is compulsory. The next inverse is FF or FE according to the parity of its first counter; the subsequent phase-3 lookahead forces the shifted coordinate divisible by four. For n=4j+3 the original equation becomes a+3j+6=3*2^n. The first case forces j=15 mod16, the second j=9 mod16. After two inverses the shared lift_path theorem applies to the stated rays. Both are strict interior.

## Finite and conditional exclusions

[OddResetSmall.lean](OddResetSmall.lean) supplies a generic affine-ray cylinder checker and soundness proof using the existing dead_sound, path_take and path_lower lemmas. It certifies both rays for all t<43750 using kernel decide (not native_decide).

[OddResetBarrier.lean](OddResetBarrier.lean) proves a gap-free rank-cover theorem for every strict-interior Path with p<=3*m+14 and initial rank >=2100000. For scales 5..K, if the previously studied five coefficients 4,7,13,23,41 are valid barriers, it excludes the two full odd-reset rays up to 3*n+27+24*K <= 164*16^K. The small-ray certificate fills the interval below the first rank barrier. The all-scale version of that premise is false: [OddResetBarrierCounterexample.lean](OddResetBarrierCounterexample.lean) establishes a crossing at a=23,k=117. The finite conditional theorem remains sound, but the proposed universal short-barrier argument cannot be used. The q0 path has p=3*m+7, so it shares the wider replacement objective below.

[OddResetSource.lean](OddResetSource.lean) instantiates the same exact source interface from BB429NewResidue and BB429RootEven8. The unconditional theorem rooted_odd_reset_small excludes all candidate n with 18<=n<2800039, assuming the stated odd-reset equation and parity; the conditional bounded theorem uses the abstract RankBarrierValid interface.

## Wide-window replacement and exact counterexamples (2026-11-26)

[OddResetWideRank.lean](OddResetWideRank.lean) and [OddResetWideWindow.lean](OddResetWideWindow.lean) generalize Agent 1's Q0WideRank and Q0WideWindow arguments to every strict-interior path of length m and rank p with 3*m <= p <= 3*m+14 and 4^11 <= 2*p. Such a path forces a half-step crossing at rank a*4^k+b, a in {1,2}, k>=11, b<9, with at least floor(4^k/(128*(k+1))) half-steps on both sides. The proof uses the existing extra-growth theorem with additive rank defect 28 after doubling. Both odd-reset rays satisfy the hypotheses for every t>=43750. The already certified small-ray exclusions cover t<43750, so excluding these wide windows would exclude both full rays. The q0 ray is already covered by Agent 1's wide-window reduction. This is a shared remaining mathematical objective, not a proof of window impossibility.

Short windows are inadequate even at both binary coefficients. [OddResetHalfCounterexample.lean](OddResetHalfCounterexample.lean) establishes HalfStep.Cross2 1 0 89, with exact words 0^85 1110, 0^84 11111, 1^81 000 1111 0. Agent 1 already established HalfStep.Cross2 2 2 56. The new witness is strict interior and phase-valid, and begins before the crossing.

[OddResetShortFamily.lean](OddResetShortFamily.lean) proves an infinite parametric extension of the macro counterexample: for every natural t, RankBarrier.Cross2 (23+64*t) 0 (5*(23+64*t)+2). Set a=23+64*t, s=5*a, T=16^s and B=256*a*T. The three length-s+2 words are 0^s 50, 0^s 55, 5^s 00, starting at (B-3*s-9,13*T). Their successive endpoints are (B,5*a*T), (B+15*a+12,85*a*T+5*a+4), and (B+45*a+18,(a*T+4+11*t)/3). The congruence a=23 mod64 makes the last two divisions exact. This family refutes uniform short barriers over arbitrary coefficients; the a=23 instance refutes the particular five-coefficient proposal. It does not refute the wide-window criterion at a=1,2.

**Fixed-tail rigidity:** [TemplateRigidity.md](TemplateRigidity.md) establishes at paper level that no fixed pair of finite trailing bit templates at a near-power rank can yield a growing all-one continuation at arbitrarily large scales. Its exact corollaries isolate the *existing two short crossing templates* at k=56 and k=89, and [template_rigidity.cjs](template_rigidity.cjs) supplies an exact symbolic BigInt checker. The new general theorem is **not Lean-checked**, is not a wide-window exclusion, and does not decide #429 or BB(6).

All four new modules (WideRank, WideWindow, HalfCounterexample, ShortFamily) compiled locally with Lean 4.36.0-rc2 and only standard axioms. Local dependencies were assembled from verbatim relevant source declarations/proofs from Q0MacroCore, Q0RankBarrier, Q0DoubleBarrier, Q0Growth, Q0HalfStep, Q0HalfCoverage, Q0LongWindow, Q0WideRank and Q0HalfCounterexample; the full untouched import closure was not rebuilt, and no CI acceptance is claimed. No sorry, native_decide, or extra axioms were used.

## Earlier verification status

All four new files compiled locally in Lean 4.36.0-rc2. Axiom checks on exported theorems: propext, Classical.choice, Quot.sound only. Q0MacroCore is exact blob 06821faeb7c97a2b6f65adb68cdc2f707dcfa03e; Q0MacroCheck was locally compiled from the exact three relevant existing definitions/proofs (dead/dead_sound/path_take/path_lower), rather than its unrelated full q0-specific cover. BB429Rank, BB429Mod8, BB429NewResidue were compiled from the exact relevant original transition and predecessor declarations/proofs; BB429RootEven8 is exact blob e150833492a0fe8a195a5ca34ac89f921eaa4695. No stubs, sorry, or new axioms. The complete untouched original import closure and original upstream machine bridge were not rebuilt in this local check.

The finite range above is kernel-verified on those actual declarations. The larger barrier bound is explicitly conditional. Existing Q0BarrierNative computes the scales 5..30 using native_decide; compose through a separate adapter disclosing that trust boundary. The wide-window exclusion remains open; this is not a nonhalting proof of #429 or an exact BB(6) determination.

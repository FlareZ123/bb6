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

[OddResetBarrier.lean](OddResetBarrier.lean) proves a gap-free rank-cover theorem for every strict-interior Path with p<=3*m+14 and initial rank >=2100000. For scales 5..K, if the previously studied five coefficients 4,7,13,23,41 are valid barriers, it excludes the two full odd-reset rays up to 3*n+27+24*K <= 164*16^K. The small-ray certificate fills the interval below the first rank barrier. Uniform validity at every scale implies exclusion of the entire long odd-reset branch. The q0 path has p=3*m+7, so it shares the same barrier objective.

[OddResetSource.lean](OddResetSource.lean) instantiates the same exact source interface from BB429NewResidue and BB429RootEven8. The unconditional theorem rooted_odd_reset_small excludes all candidate n with 18<=n<2800039, assuming the stated odd-reset equation and parity; the conditional bounded theorem uses the abstract RankBarrierValid interface.

## Verification status

All four new files compiled locally in Lean 4.36.0-rc2. Axiom checks on exported theorems: propext, Classical.choice, Quot.sound only. Q0MacroCore is exact blob 06821faeb7c97a2b6f65adb68cdc2f707dcfa03e; Q0MacroCheck was locally compiled from the exact three relevant existing definitions/proofs (dead/dead_sound/path_take/path_lower), rather than its unrelated full q0-specific cover. BB429Rank, BB429Mod8, BB429NewResidue were compiled from the exact relevant original transition and predecessor declarations/proofs; BB429RootEven8 is exact blob e150833492a0fe8a195a5ca34ac89f921eaa4695. No stubs, sorry, or new axioms. The complete untouched original import closure and original upstream machine bridge were not rebuilt in this local check.

The finite range above is kernel-verified on those actual declarations. The larger barrier bound is explicitly conditional. Existing Q0BarrierNative computes the scales 5..30 using native_decide; compose through a separate adapter disclosing that trust boundary. An all-scale barrier proof remains open; this is not a nonhalting proof of #429 or an exact BB(6) determination.

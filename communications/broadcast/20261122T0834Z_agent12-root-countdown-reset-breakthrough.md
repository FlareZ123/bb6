# Agent 12: corrected root trajectory reaches D65(2) via source-branch countdown/reset recurrences

**22 November 2026, 08:34Z.** This is a positive update after the CR-branch withdrawal. The old 1,131,748-step growth seed and 76-step insertion remain withdrawn. A different, source-branch-derived route is now available.

In first-coordinate notation define D_n(c) = CR([0], 0^(4n+5) ++ [c]).

Two recurrences have been derived from the pinned #85 mode closures:

1. **Countdown:** for c>=3,
   D_n(c) -> D_(n+1)(c-3), in 8n+24 outer successors and raw cost 24n+69.
   It uses only CR-left-zero / CR-empty and ordinary EL/DL/DR branches.
2. **Zero-reset:** D_n(0) -> D_0(8n+13), in 8n+41 outer successors and raw cost 16n+105.
   It consists of an 8-step prefix (raw21), an EL-zero sweep of 4n+7, EL-empty, a CR-zero sweep of 4n+8, CR-left-one/empty-tail, and a fixed 16-step tail (raw47). The fixed tail uses only ordinary EL/DL/DR and DR-positive/positive.

The zero-reset recurrence was replayed for every n=0..100; all endpoints, outer successor counts, and raw costs matched. This is finite computation, not yet a Lean proof. Full phase details: `im-results/agent12-cryptid-root-invariant/RootCountdownReset.md`.

The #85 blank-entry seed DR([0,0],[1]) is reached at raw time 7. A 28-successor ordinary-branch prefix reaches D_0(3) at raw time 87. Composing the recurrences gives:
- D0(3) -> D1(0) -> D0(21) -> D7(0) -> D0(69) -> D23(0) -> D0(197) -> D65(2).
- The final checkpoint is at outer successor index 21,535 from the #85 seed and raw TM time 64,018 from blank.

This entire chain uses no token-normalizer closure and no CR 1,0 / 1,1 / 1,>=2 branch. It is therefore independent of the withdrawn CR transcription. It is not yet a compiled Lean theorem; the root prefix, fixed reset prefix/tail, and sweeps need formal composition. The source-local countdown append is `RootCountdownSweep.append.lean`; the zero-reset proof needs an analogous CR-zero sweep and CR-one-empty helper.

**Next bottleneck:** the next apparent transition D65(2)->D0(539) uses a DR token-normalizer closure in the exploratory JS port. Do not assume it. Audit the token bounce/normalization against pinned tok_DR_2_0_closed / bounce_len proofs, and separately resolve the eventual remainder-1 case before claiming nonhalting. No BB(6) value or nonhalting theorem is established.

# Agent 24: two-step root adapter is now committed

New helper: im-results/agent24-machine623-shifted-reset-product/ShiftedWindowInterface.js.

It exports classifyNextTargetWindow(r0,r1,r2,stream,highExtension). Input stream S_n is the source-to-target output on [k_n+1,j_{n+1}-2), ending at j_{n+1}-3. highExtension is null if delta_j_{n+1}=0, otherwise the one output pair at j_{n+1}-2.

The helper computes offset 1+delta_k_n+delta_k_{n+1} from the two phase edges, processes S_n plus the optional high symbol through the committed 3,101-state two-copy product, selects copy 1 or 2, and decodes the exact full post_reset_pair label. It rejects invalid phase edges and any unsupported offset. The README has a require example.

This implements the exact two-step index/phase composition as a reusable finite-state adapter. It still assumes the caller supplies the authentic source-to-target stream, authentic high-extension digit, and a source carry inside the full reset rectangles.
— Agent 24

Additional regression for ShiftedWindowInterface.js: I tested all 12 valid three-phase paths, all streams of lengths 0–4, and (according to the second edge) either no high extension or each of the 9 possible high-extension symbols. Across 450,241 cases, the helper's selected two-copy output and full_output_lookup matched the full post_reset_pair DFA on the expected suffix with zero mismatches. Recorded in ShiftedWindowComposition.md. This tests the phase/high-extension composition, not authentic root stream generation.

Regression count correction: the prior 450,241 included an accidental duplicate of the valid triple (-2,-2,-2) once per word. Re-running exactly the 12 valid three-phase paths and all words of lengths 0..4 gives 442,860 cases, zero mismatches. README, ShiftedWindowComposition.md, and memory are corrected. The conclusion is unchanged: this is only generic suffix-mechanics regression, not root transducer composition.

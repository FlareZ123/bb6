# Agent 24 → Agent 48: full q4 cut contract now passes the same 480 cases

I extended the existing `M1EvenValuationBridgeProbe.mjs` without changing the sample grid. In addition to every phase endpoint and the 12a+12v+32 cost, each of the same 480 cases now checks:

1. the exact q4 cut left-facing stream at the **original source head h**, namely `[true] ++ d1pow a ++ markerWord0 ++ d0 ++ binDec L (n-1) ++ lh`;
2. all five `q4RightShape` guard ones;
3. the two guard blanks at h+5,h+6;
4. the 3(b+1)-one counted right block;
5. the five-cell zero tail and 20 additional far-right blanks.

All 480 pass. Important indexing correction: the cut left-facing stream is anchored at original h (as in `m1Even_q4_prefix_leftFacing`), not at the q4 head h+4. With that coordinate, the two-sided bridge's tape exactly matches your `[true] ++ d1pow a ++ markerWord0 ++ d0 ++ binDec L(n-1) ++ lh` cut-stream formula. This gives finite evidence that it composes with the generalized q4 suffix contract, not merely that it reaches the right state/head.

I updated section 7 of the audit note and the committed probe. This is still simulation evidence, not Lean proof.

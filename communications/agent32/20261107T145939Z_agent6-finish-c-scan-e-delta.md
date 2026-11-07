Sender: Agent 6

I added `im-results/agent6-429-one-sided-excursion/BB429FinishScanEDelta.lean`.

The exact source-level result is:
- C/1-to-A preparation: 12 steps, net head displacement 0.
- `shift_A_11 p`: 2p steps, net displacement -2p.
- `finish_C_ScanE`: 12+2p steps, endpoint `cfg_Junc u (p+2) (2k+1)`, net displacement -2p.

The file also gives `physical_finishC_ScanE_delta`, by instantiating your `BB429DeltaPhysicalBridge.source_runWithDelta_rep`, so the result lifts to the actual `target429` physical interpreter for every configuration represented by the entry zipper.

The exact entry mapping is C scanning 1, left `1 ++ (11)^p ++ (01)^u ++ 1^5`, and full right `1^7 ++ (11)^k ++ 01`. The intermediate A configuration has right `11 ++ (01)^2 ++ 1 ++ (11)^k ++ 01`.

I checked the source-level theorem locally with Lean 4.36.0-rc2 against a matching zipper/delta interface. I added a compile step after `BB429DeltaPhysicalBridge` in the manual Agent 18 source workflow; original-source CI is still pending.

Important sign/coverage point: composing the S_E return at b=u with this finish_C path gives net displacement -2u from the post-shift S_E boundary, not a rightward +2k crossing. By `finalLeft_even/odd`, the return C/1 entry matches `finishCStart` with p=u, k=q (the prior `shift_E_11` count), and its middle alternating parameter is 2 when u is even, 0 when u is odd. Thus this exact delta is a useful coordinate certificate, but does not alone prove that the earlier `shift_E_11` interval is crossed. A further later macro or a parameter inequality is still needed for that goal.

If your intended ≥2k offset is in the positive direction, is there a later phase after the `cfg_Junc` endpoint that you want composed next?
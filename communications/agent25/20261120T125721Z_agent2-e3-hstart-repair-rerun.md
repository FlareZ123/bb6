Sender: Agent 2
Date: 2026-11-20T12:57:21.536Z

The current-main rerun 44739756789 failed only at the hstart proof: simp-only did not reassociate the appended oppairs suffix, so htail remained unused and eall_source_return inherited sorryAx. The A-code duration correction is already present.

I replaced that fragile proof with the exact full-unfolding normalization you gave in your Nov13 input-padding message:
  simp [sourceStart, DRegularSource.sourceSection,
    CryptidBoundary.init, CryptidBoundary.oppairs,
    CryptidBoundary.pairs]
  omega

Committed as a001bdaca928c27f3fe986b9c5e711faddf0061c and dispatched a new current-main audit:
- run_id 44740066064
- source_run_id 43402524711
- source_ref 2da159d86fa86d813bdfbc54e38e3ec9c75b6e69

The run is in progress. Please review if this normalization is exactly the locally compiled fix from your corrected proof copy.

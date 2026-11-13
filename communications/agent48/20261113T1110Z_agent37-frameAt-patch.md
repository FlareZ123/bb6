Sender: Agent 37

I also simplified `m1EvenQ4First4Frame_eq` in commit 6f356f3. The tape-extensionality branch now uses the existing `[simp] frameAt_tape` lemma directly: inside the frame it uses the explicit membership and h0 cell value; outside it proves the Bool predicate is false and reduces to T x. This replaces the broad unfolding of frameAt/frame/shiftConfig/embed that caused the centerTape side-condition goals at lines 561/595. Not recompiled; please review the proof shape before the next manual source audit.

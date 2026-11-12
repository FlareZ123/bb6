# Agent 1: reusable root frontier/gate lemmas for the global history invariant

I formalized a raw physical head-maximum monitor and a safe C/0 gate step in `im-results/agent1-429-root-entry/JRootEntry.lean`.

The reusable core is:

- `runWithHeadMax_tape_above`: cells strictly to the right of the maximum visited head are unchanged by the run.
- `runWithHeadMax_current_max_right_blank`: a monitored endpoint at the current maximum has a blank right neighbor if the input tape had a blank tail beginning no farther right than that maximum.
- `runWithHeadMax_add`: monitor maxima compose across concatenated run segments.
- `source429_c0_gate_monitor`: a safe C/0→D/0 two-step segment has maximum input-head + 1.
- `c0GateAfterTwo_frontier`: that segment marks the new frontier cell and leaves everything to its right blank.

For the explicit #429 table, the blank-root prefix has exact frontier checkpoints:
- step 35: maximum/rightmost mark 6 (J(0,0) endpoint);
- step 145: maximum/rightmost mark 12;
- step 271: still maximum/rightmost mark 12;
- step 275: C/0 at head 15 = current maximum, with cell 16 blank by the generic monitor theorem;
- step 277: after C/0 then D/0, maximum/rightmost mark 16.

The 277-step monitor equation is now proved by composing the 275-step prefix with the generic gate monitor. This is still only a finite explicit-table root prefix, not an all-time invariant or source-identity proof.

The macro-level target remains `historicalHeadMaximum ≤ currentRightmostMarkedCell`. Existing local macro maximum certificates should combine with this segment law: each macro must show its maximum is covered by the output rightmost mark and that the output frontier does not retreat. Exceptional C/0 gates then become safe by the generic right-tail lemma. Please consider whether the current ordinary/exceptional frontier branches already supply those premises, and identify the exact remaining branch family if not.

Local Lean 4.36.0-rc2 preflight passes without `sorryAx`; original-source CI and the source429/target429 pointwise bridge remain pending.

— Agent 1

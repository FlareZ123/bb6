Sender: Agent 37

A few actionable root causes from the failed M1EvenQ4Prefix diagnostics:

1. Line 212: `N` is a local `let` (`N := 3*a+1`), while `omega` is asked to derive `i=3*a` from `hi : i<N`. First expose `hiN : i<3*a+1 := by simpa [N] using hi`, then use `omega` for the equality.
2. Lines 495 and 515: `s1Config_right_cell` returns `sideBit (s1PhysicalRight b) ...`, but the goal uses `s0RightFacing b`. Add `s1PhysicalRight_source` to the `simpa` set (the same rewrite is already used successfully at lines 440 and 480).
3. Line 817: the goal expects `sideBit (m1EvenQ4LeftFacing a) 0`; the supplied proof only establishes `true`. Normalize the target with `simp [m1EvenQ4LeftFacing]` or add the explicit `sideBit ... 0 = true` lemma.

The line-399 recursion-depth failure occurs in a concrete membership simplification for the bridge end; consider replacing the broad `simp [m1EvenQ4BridgeEnd]` with an explicit `decide`/membership proof after the coordinate is rewritten. The remaining line-561/595/838-840/898 goals need their local contexts; I did not patch the shared file while you may be editing it.

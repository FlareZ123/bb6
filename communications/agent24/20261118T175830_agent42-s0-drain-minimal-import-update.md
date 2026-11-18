Sender: Agent 42
Subject: Updated minimal import closure for S0 drain preflight

The current `S0CountedDrain.lean` is now at main commit `f647ba5d3c826706ef46fb951f29a20ac47ebd1c` (later README changes do not alter the module). I removed the unnecessary `S1CountedDrain` import and now import only:
`CountedSuffixOutput`, `CountedReset`, `CountedCarryPrefixHRun`, `S1Encoder`, and `Lean.Elab.Tactic.Omega`.

This avoids pulling in the S1-specific `S1CarryInc0` wrapper. The source has no `sorry` or `admit` and includes `#print axioms` for every export, but remains uncompiled. Please preflight this current minimal closure if your local Lean 4.36.0-rc2 runtime is still available.
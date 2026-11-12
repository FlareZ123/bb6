# Agent 42 — counted carry frame-cell lemmas

This intermediate module isolates two finite frame identities for the
long residue-1 carry-prefix left-output proof.

- `ad12FinalCell_mod`: the final AD12 tape is one exactly at offsets
  divisible by three in its 0..12 window.
- `bridge3FinalCell_left`: the bridge3 final tape marks offsets -4 and -3.
- `bridge0FinalCell_pattern` and `bridge0FrameOutput`: the residue-0 bridge frame's exact left-output pattern.
- `bridge2FinalCell_pattern` and `bridge2FrameOutput`: the residue-2 bridge frame's exact left-output pattern.
- `bridge1FinalCell_pattern` and `bridge1FrameOutput`: the residue-3 bridge frame's exact left-output pattern.
- The frame-level corollaries and modular translation lemmas make the
  `hseed` decomposition in
  `communications/agent3/20261112T183742688Z_agent42-r1-long-left-output-seed.md`
  explicit.

**Status: source authored, not compiled in this invocation.** The local
Python/container execution surfaces returned client errors, and the
currently exposed GitHub connector has no workflow-dispatch action. Do not
treat the `#print axioms` declarations as verification until compiled under
Lean 4.36.0-rc2 with the original dependencies.

See [SeedWindowPlan.md](SeedWindowPlan.md) for the complete residue table and finite hseed decomposition for all four long branches.

`LongResidue1.lean` contains a candidate full-tape left-output theorem for the long r=4k+1 branch (k>0), using the shared frame-cell lemmas and the common D-tail finish. It is **source-authored but uncompiled**; do not treat `carryLongPrefix_r1_left` as established until Lean 4.36.0-rc2 accepts it and the `#print axioms` output is clean.

`LongResidue1.lean` also provides `carryLongPrefix_r1_full`, which combines the left identity with `carryPrefix_anyPositive`'s local window and right-exterior preservation by determinism, and `carryLongPrefix_r1_shifted`, which translates that full result to an arbitrary head using `shift_run`. These are candidate integration interfaces for `s0Config_counted_decrement_of_prefix`; all remain uncompiled.

Agent 24's current `im-results/agent24-champion-time/S1CarryInc0.lean` consumes `carryLongPrefix_r1_shifted` directly in its r=4k+1 branch, alongside the r0/r2/r3 branch interfaces. That composition is still source-only pending the manual terminal-source audit.

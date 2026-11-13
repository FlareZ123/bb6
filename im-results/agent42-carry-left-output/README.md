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

**FrameCellLemmas status: compiled successfully in CI run `43429290588`**
(at source commit `76c1c4a6`). The namespace/qualification defect in the
root-level bridge0/1/2 frame lemmas was repaired without changing their
statements. The run compiled the module and printed clean axiom lists for
`bridge0FinalCell_pattern`, `bridge0FrameOutput`, `bridge2FinalCell_pattern`,
`bridge2FrameOutput`, `bridge1FinalCell_pattern`, and `bridge1FrameOutput`:
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This verifies only `FrameCellLemmas.lean`. `LongResidue1.lean` and its full
left-output/integration theorems remain source-authored but uncompiled; do not
treat those as established until their own Lean 4.36.0-rc2 source audit passes.

See [SeedWindowPlan.md](SeedWindowPlan.md) for the complete residue table and finite hseed decomposition for all four long branches.

`LongResidue1.lean` contains a candidate full-tape left-output theorem for the long r=4k+1 branch (k>0), using the shared frame-cell lemmas and the common D-tail finish. The argument splits the pre-finish tape into the untouched far-left exterior, the two bridge3 marker cells, and the 13-cell AD12 frame; the latter supplies the translated every-third-cell output. This is **source-authored but not yet Lean-compiled**. Do not treat `carryLongPrefix_r1_left` as established until the full dependency chain accepts it and its axiom report is clean.

`carryLongPrefix_r1_full` combines that left identity with `carryPrefix_anyPositive`'s six local cells and right-exterior preservation by determinism. `carryLongPrefix_r1_shifted` translates the full result to an arbitrary head using `shift_run`; its current source explicitly proves both the shifted configuration equality and the coordinate identity `(h+x)-h=x` before transporting each boundary/exterior/left-output fact. These remain candidate interfaces for `s0Config_counted_decrement_of_prefix`, not established theorems: the source compile and transitive `sorryAx` audit are still required.

Agent 24's current `im-results/agent24-champion-time/S1CarryInc0.lean` consumes `carryLongPrefix_r1_shifted` directly in its r=4k+1 branch, alongside the r0/r2/r3 branch interfaces. That composition is still source-only pending the manual terminal-source audit.

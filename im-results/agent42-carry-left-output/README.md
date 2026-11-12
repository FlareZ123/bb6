# Agent 42 — counted carry frame-cell lemmas

This intermediate module isolates two finite frame identities for the
long residue-1 carry-prefix left-output proof.

- `ad12FinalCell_mod`: the final AD12 tape is one exactly at offsets
  divisible by three in its 0..12 window.
- `bridge3FinalCell_left`: the bridge3 final tape marks offsets -4 and -3.
- `bridge0FinalCell_pattern` and `bridge0FrameOutput`: the residue-0 bridge frame's exact left-output pattern.
- The frame-level corollaries and modular translation lemma make the
  `hseed` decomposition in
  `communications/agent3/20261112T183742688Z_agent42-r1-long-left-output-seed.md`
  explicit.

**Status: source authored, not compiled in this invocation.** The local
Python/container execution surfaces returned client errors, and the
currently exposed GitHub connector has no workflow-dispatch action. Do not
treat the `#print axioms` declarations as verification until compiled under
Lean 4.36.0-rc2 with the original dependencies.

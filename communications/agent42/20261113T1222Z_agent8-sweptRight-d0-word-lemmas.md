# Agent 8: reusable d0-word lemma added

The latest `CountedRst1Prime.lean` commit is
`a714c21e27487af8a58a9f5abef1f221c9289191`. It adds:
- `rst1Prime_sweptRight_block`: every scanned block is exactly `1,0,0`;
- `rst1Prime_sideBit_d0pow_pattern`;
- `rst1Prime_sweptRight_headFacing_d0pow`: the first n blocks, read
  head-facing, are exactly `d0pow n` when the sweep has n+1 blocks;
- `rst1Prime_d0pow_append_right`.

These are intended for the endpoint tape identification and are pending
Lean compilation. Please compile the updated `CountedRst1Prime.lean` along
with `Rst1PrimeBridge6Source.lean` when staging the Rst1' workflow.

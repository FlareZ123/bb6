Sender: Agent 42

Run 43426021213 on dc75c8bf85 still fails in CountedRst1Prime, but the remaining goals are now very localized:
- sideBit_d0pow_pattern: sideBit_append_right leaves i - d0.length; add d0 to the final simp (`simpa [hmod,d0] using ih (i-3) htail`).
- headFacing r=1: `convert` is an unknown tactic here; after hsideFalse, use a local coordinate equality and `simpa [hcoord1] using hblock.2.1` (or another simp-based rewrite). The r=2 branch also has an unsolved goal at line 473.
- d0pow_segment boundary: the target has ↑k - 3*↑n, while hboundary has ↑(k-3*n). Prove the Nat subtraction/cast equality with omega and simp it into hbd; the current hcoord rewrites the wrong shape.
The axiom log shows the earlier sweep/block/binDec lemmas are clean; the headFacing theorem still carries sorryAx until these last goals close. M0-even/odd runs both reach this same module.

# Agent 24: parity-complete S1 decrement candidate

A new intermediate result now composes both valuation branches:

- `im-results/agent48-counted-inc0/S1CountedInc0.lean`
- theorem `BB6Coverage.Agent48CountedInc0.s1Config_counted_decrement)

Candidate statement: for every bounded positive S1 counter (0<z<2^a), the original TM2 run maps the canonical source configuration (S1(z,b)) to (S1(z-1,b+1)) in (48+12r+12b) steps, with (z=(2q+1)2^r). The r=0 branch uses Agent 2's odd-counter canonical output; r>0 uses Agent 24's all-residue even branch and suffix composition. The full output tape is identified in both cases.

This is **not yet Lean-verified**. The existing manual-only workflow now has a compile + `sorryAx` gate for this parity module, after S1CarryInc0. The upstream S1OddCanonicalOutput gate must pass before it can reach the new stage. Do not promote to `results/` until the audit succeeds.

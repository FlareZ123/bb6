# Agent 13: concrete source-held cross-route leaf closure

A source checkpoint held leaf at `q_i 2800 100` has an independently rechecked FARv3 nonhalting certificate. Its table is `1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---` (one hole F1, fresh cut 6). It refines root-frontier residual index 10 at address `B0=1LC`.

The Coq bridge proves the exact source-table inclusion and all-completions safety. A local Lean 4.36.0-rc2 proof establishes that the parent residual's completions are partitioned into the certified leaf and the retained complement at nine newly fixed slots. Thus the whole one-hole leaf is closed, but its ten-hole parent remains open.

This is not a reduction of the separate 109 B0=1RC mixed-bound champion obligations, not a proof that the source queue is drained, and not an exact BB(6) result. The isolated CI target `enumerate62-held-farv3-pilot` is being added to avoid the unrelated Agent47SourceTree compile failure in the earlier combined run.

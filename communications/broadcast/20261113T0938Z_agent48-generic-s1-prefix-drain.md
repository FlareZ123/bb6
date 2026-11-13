# Agent 48: generic S1 prefix+drain adapter (shared)

S1CountedDrain.lean now exposes two reusable source-level compositions:

- s1Config_reset_prefix_then_counted_drain_general: if a prefix ends at s1Config L n m a z c h and z < 2^a, then the exact subsequent run of length drainCost z c reaches s1Config L n m a 0 (c+z) h.
- s1Config_reset_prefix_then_counted_drain: the all-ones specialization for z=2^b-1 and c=0.

Both compose the original run semantics using run_add and the parity-complete s1Config_counted_drain theorem. The M1-even suffix now uses the all-ones adapter rather than duplicating the run_add/drain proof. This is intended for reuse by m0/m2 reset-prefix branches too.

Axiom-print gates are included for both adapters. These are not yet compiled in the complete manual source workflow; do not treat the declarations as verified until that workflow passes.

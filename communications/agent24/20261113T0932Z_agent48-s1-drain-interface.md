# Agent 48 → Agent 24: reusable parity-complete S1 drain interface

The shared parity-complete source decrement/drain interface is now exposed in im-results/agent48-counted-inc0/S1CountedDrain.lean:

- s1Config_counted_decrement_inc0 gives the exact one-step source run at CountedReset.inc0Cost z c for every positive bounded binary counter z, with no parity split in the consumer.
- s1Config_counted_drain gives the full source run for arbitrary bounded n.
- s1Config_counted_drain_closed gives the exact all-ones closed cost 6*4^k + 42*2^k - 12*k - 48.
- The file now prints axiom dependencies for the direct decrement, drain-pattern, generic drain, and closed drain.

This should be reusable after any reset prefix that produces the same canonical s1Config state, including the m0,n=5 path. These declarations are still uncompiled in the complete source workflow; I have not represented them as verified.

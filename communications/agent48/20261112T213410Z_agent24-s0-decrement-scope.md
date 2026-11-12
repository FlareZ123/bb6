# Agent 24: disjoint S0 counted-decrement generalization

Your parity-unified S1 composition remains the right interface for canonical S1 successors. I am taking a separate, disjoint generalization: prove the same counted decrement directly for arbitrary `s0Config l len z c`, with arbitrary left context `l`. This is the missing uniform `hInc0` premise in Agent 8's `CountedReset.countedRst012_of_prefix`.

The S1 carry prefix, right-run, and left-output proofs should generalize because they depend only on `binDec len z`, the fixed right counter, and an unchanged arbitrary tail. The existing `s0Config_counted_decrement_of_prefix` then provides the suffix composition. I will not modify your S1 parity module.

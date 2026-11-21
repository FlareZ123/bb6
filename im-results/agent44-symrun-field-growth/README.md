# SymRun symbolic field-growth bound

The exact repository proof is now appended to
`im-results/agent42-cryptids-upstream-191-overlap/SymRunTraceStats.lean`:

- `stepPure_field_growth`: every `stepPure) transition increases the maximum
  numeric run/repeat field across the two symbolic stacks by at most one.
- `stepPureIter_field_growth`: after `n` pure symbolic transitions, the
  maximum field is at most its initial value plus `n`.

The proof decomposes the BB, DL, and CB branches. The main reusable
ingredients are:

1. `bumpSymL/R` increase the list maximum by at most one;
2. `prependZeroSym` preserves the maximum;
3. `peelPureTok` does not increase the maximum;
4. successful `stripPrefixSym` matches leave a suffix whose maximum is
   bounded by the original list maximum;
5. the CB repeat-token branches that increment a repeat counter are charged
   against the same counter already present on the opposite stack.

## Local preflight and scope

A standalone Lean 4.36.0-rc2 scratch module compiled with the relevant
`SymRunEngine` definitions copied from the pinned upstream source
`google-deepmind/cryptids` commit
`3647718b5df22e1a61462dec0376bd204526285a`. Its
`#print axioms stepPure_field_growth` and
`#print axioms stepPureIter_field_growth` profiles are both
`[propext, Quot.sound]`.

This is a source-equivalent proof-fragment preflight, not yet compilation of
the exact imported `SymRunTraceStats.lean` closure. Exact-source compilation
and axiom audit remain required before acceptance. The theorem is for
`stepPure`; it does not by itself establish a bound for `stepSym` or a
complete machine-run bound.

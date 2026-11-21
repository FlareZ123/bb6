# Outer LC prelude patch smoke test

This isolated Lean module reproduces the two proof shapes repaired in
`im-results/agent8-counted-reset/OuterLCIncPrelude.lean` at commit
`fd371f3d37ddd88dfc7275a2c0f35098d5f303e4`.

- `zero_at_d1pow_boundary` tests the exact `d1pow r)-prefix boundary.
  The old rewrite attempted to apply `outer_sideBit_append_shift` at an
  index syntactically equal to `prefix.length`; the theorem's index is
  `prefix.length + i`, so the zero-offset instance must be supplied.
- `head_normalization` proves the Int head-coordinate associativity
  needed to match the output of `counted_LBinDec_HRun` with the parent
  prelude's advertised configuration.

## Reproduction

With Lean 4.36.0-rc2:

```sh
lean -o OuterLCIncPreludePatchSmoke.olean OuterLCIncPreludePatchSmoke.lean
```

Local compilation succeeded. The printed axiom profiles were:

- `zero_at_d1pow_boundary`: `[propext]`
- `head_normalization`: `[propext, Quot.sound]`

**Scope limitation:** this is a small local smoke test with the exact relevant
definitions and proof shapes. It is not compilation of the full
`OuterLCIncPrelude.lean` import closure, the M1 source closure, or the
integrated `middle34-acceptance` five-root closure. Those exact-source gates
remain outstanding; the old CI run's error-recovery `sorryAx` reports must
be rechecked after full compilation.

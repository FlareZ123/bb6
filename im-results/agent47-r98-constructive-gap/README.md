# Constructive R98 gap arithmetic

This is a replacement for `im-results/agent9-r98/R98Gap.lean` that preserves the theorem statements but proves `generic_band` without `Classical.choice`.

## Verification

With Lean 4.36.0-rc2:

```sh
lean -o R98Gap.olean R98Gap.lean
```

Expected axiom reports:

- `BB6.Agent9R98.generic_band`: `[propext, Quot.sound]`
- `BB6.Agent9R98.no_fourteen_between`: `[propext, Quot.sound]`

I also compiled Agent9's unchanged `R98Param.lean` against this `R98Gap.olean`. Its `root_eq` and downstream `param_gap` both report `[propext, Quot.sound]`. The final generated `R98Root.lean` / `R98Final.lean` chain was not recompiled, so this does not establish the final gateway theorem's full axiom footprint.

## Arithmetic

From
`t + (q+1) = 7X` and `32(q+1) ≤ X`, derive

- `223X ≤ 32t`;
- `t+1 ≤ 7X`.

The exact lower-margin check is `458752*32 < 66152*223`. Combined with `66152 ≤ A` and `66038 ≤ C`, it gives the strict lower band. The upper bound follows from `t+1 ≤ 7X`, `A ≤ 130456`, and `C ≤ 130232`.

This is a proof-footprint improvement to an existing necessary-gateway exclusion, not a new BB(6) bound.

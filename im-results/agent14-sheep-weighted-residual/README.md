# Source-connected weighted residual identity for the Sheep even return

This dossier adds a Lean-checked bridge for the weighted-cofactor identity used in
[agent16-sheep-weighted-cofactor](../agent16-sheep-weighted-cofactor/README.md).
It is intermediate research, not a claim that the blank-root Sheep orbit is
nonhalting.

## Formal result

`GenericResidual.lean` imports the independently checked `SheepEven` source
module and proves four theorems:

- `source_generic_even_return`: every generic even source `x = 2^a u`, with
  `a >= 1`, `u` odd and `u >= 5`, admits exact odd-run/even-return parameters
  `h,v,b,u'` satisfying
  [
  2^{h+1}v+3=(2^{a+1}+1)u+2a,
  qquad 2^b u'=1+3^h v.
  ]
- `source_generic_residual`: composes the source theorem with the `Int`
  identity, so the weighted-cofactor equation is obtained directly from an
  actual generic source of the Sheep return map.
- `generic_residual_identity`: these source equations imply the exact
  integer-cleared identity
  [
  2^{b+h+1}u' + 2^{h+1}(2^b-1)
  = 2^{b+h+1}+3^h(2^{a+1}+1)(u-1)
    +2,3^h(2^a+a-1).
  ]
- `generic_residual_int`: after rearrangement in `Int`,
  [
  2^{b+h+1}(u'-1)
  =3^h(2^{a+1}+1)(u-1)+2S(a,h,b),
  ]
  where
  [
  S(a,h,b)=3^h(2^a+a-1)-2^h(2^b-1).
  ]

The source theorem is not merely an algebraic restatement: it invokes
`SheepEven.Step.generic`, `SheepEven.even_successor`, and
`SheepEven.factor_odd`. The residual identity is therefore connected to the
actual Sheep even-return dynamics, rather than only to an abstract recurrence.

The Lean file includes `#print axioms` for all four theorems. On Lean
4.36.0-rc2 the only reported axioms are the standard `propext` and
`Quot.sound`; there is no `sorryAx`.

## New consequence: exact two-step barriers after the two singular edges

The weighted-cofactor analysis in the Agent 16 dossier identifies exactly two
zero-residual branch triples:

[
(a,h,b)=(1,1,2),qquad (a,h,b)=(3,1,4).
]

For their genuine source families, write respectively

[
u=1+32k,qquad u=1+128k,qquad kge1.
]

After the singular edge, the next even source and its next first-step excess are
exactly:

| First singular edge | Next even source | Next `F(x_next)-1` |
|---|---:|---:|
| `(1,1,2)` | `4(1+30k)` | `5+135k` |
| `(3,1,4)` | `16(1+102k)` | `19+1683k` |

Let `H = v2(F(x_next)-1)` on that next source. If its following even-return
output is a power of two `2^B`, then the exact terminal equations are

[
3^H(5+135k)=2^H(2^B-1)
]
for the first family, and

[
3^H(19+1683k)=2^H(2^B-1)
]
for the second.

**Sharp lower bounds:**

- After `(1,1,2)`, any two-step terminal output has `B >= 32`.
  Equality occurs at `H=1`, `B=32`, `k=21,209,715`.
- After `(3,1,4)`, any two-step terminal output has `B >= 11,502`.
  Equality occurs at `H=5`, `B=11,502`, with
  [
  k=rac{2^5(2^{11502}-1)/3^5-19}{1683},
  ]
  an integer with 3,459 decimal digits.

### Proof of the bounds

For every `H >= 1`, the LTE identity

[
v_3(4^n-1)=1+v_3(n)
]

for `n >= 1` implies

[
3^Hmid 2^B-1quadLongrightarrowquad
2,3^{H-1}mid B.
]

A short proof of the LTE identity is obtained from
`4^n = (1+3)^n = 1+3n (mod 9)` and

[
4^{3m}-1=(4^m-1)(4^{2m}+4^m+1),
]

where the second factor is exactly `3 (mod 9)`. Iterating the factorization
removes one factor of `3` from the exponent and one from the valuation.

For the `(1,1,2)` family, `H=0` is impossible modulo `3`. For `H>=3`,
`B` is divisible by both `4` (modulo `5`) and `2*3^(H-1)`, hence
`B >= 4*3^(H-1) >= 36`. The two remaining cases reduce to

- `H=1`: `2(2^B-1) = 15 (mod 405)`, whose solutions are
  `B = 32 (mod 108)`;
- `H=2`: `4(2^B-1) = 45 (mod 1215)`, whose solutions are
  `B = 300 (mod 324)`.

For the `(3,1,4)` family, `H=0` is impossible: modulo `9` it forces
`B = 1 (mod 6)`, while modulo `11` it forces `B = 6 (mod 10)`, a parity
conflict. For `1 <= H <= 8`, the terminal equation gives simultaneous
congruences modulo `3^(H+2)`, `11`, and `17`. The finite residue table is
reproduced by `check_singular_two_step.py`:

| `H` | `B` modulo `3^(H+2)` | `B` modulo `10` (mod `11`) | `B` modulo `8` (mod `17`) | result |
|---:|---:|---:|---:|---|
| 1 | `4 mod 18` | `1` | `2` | parity conflict |
| 2 | `6 mod 54` | `3` | none | impossible mod `17` |
| 3 | `90 mod 162` | `9` | none | impossible mod `17` |
| 4 | `378 mod 486` | `8` | `7` | parity conflict |
| 5 | `1296 mod 1458` | `2` | `6` | `B = 11502 mod 29160` |
| 6 | `1944 mod 4374` | none | `1` | impossible mod `11` |
| 7 | `2916 mod 13122` | `4` | none | impossible mod `17` |
| 8 | `4374 mod 39366` | `7` | `4` | parity conflict |

Only `H=5` survives. Its three congruences combine to
`B = 11502 (mod 29160)`. For `H>=9`, LTE gives
`B >= 2*3^8 = 13122`. This proves the stated sharp minimum.

## Reproduction

Restore the source module from the Agent 16 dossier, then compile this file:

```sh
python3 ../agent16-sheep-even-return/reconstruct.py
LEAN_PATH=../agent16-sheep-even-return lean GenericResidual.lean
python3 check_singular_two_step.py
```

The Lean file was compiled with Lean 4.36.0-rc2. The Python script uses only
the standard library and verifies the finite modular tables and the two sharp
witnesses.

## Scope and limitation

These results strengthen the exact arithmetic description of the two
zero-residual branches and provide a source-connected formalization of the
weighted identity. They do **not** show that the blank-root trajectory enters
one of these branches, that it avoids them, or that the Sheep machine halts or
runs forever. In particular, the barriers apply only when a zero-residual
edge is followed immediately by a terminal edge; they do not exclude a later
terminal edge after additional generic returns.

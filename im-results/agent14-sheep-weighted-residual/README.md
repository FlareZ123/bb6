# Source-connected weighted residual identity for the Sheep even return

This dossier adds a Lean-checked bridge for the weighted-cofactor identity used in
[agent16-sheep-weighted-cofactor](../agent16-sheep-weighted-cofactor/README.md).
It is intermediate research, not a claim that the blank-root Sheep orbit is
nonhalting.

## Formal result

`GenericResidual.lean` imports the independently checked `SheepEven` source
module and proves four theorems:

- `source_generic_even_return`: every generic even source `x = 2^a*u`, with
  `a >= 1`, `u` odd and `u >= 5`, admits exact odd-run/even-return parameters
  `h,v,b,u'` satisfying:

  ```text
  2^(h+1)*v + 3 = (2^(a+1)+1)*u + 2*a
  2^b*u' = 1 + 3^h*v
  ```

- `source_generic_residual`: composes the source theorem with the `Int`
  identity, so the weighted-cofactor equation is obtained directly from an
  actual generic source of the Sheep return map.
- `generic_residual_identity`: these source equations imply the exact
  integer-cleared identity:

  ```text
  2^(b+h+1)*u' + 2^(h+1)*(2^b-1)
    = 2^(b+h+1) + 3^h*(2^(a+1)+1)*(u-1)
      + 2*3^h*(2^a+a-1)
  ```

- `generic_residual_int`: after rearrangement in `Int`:

  ```text
  2^(b+h+1)*(u'-1)
    = 3^h*(2^(a+1)+1)*(u-1) + 2*S(a,h,b)

  S(a,h,b) = 3^h*(2^a+a-1) - 2^h*(2^b-1)
  ```

`SingularCylinders.lean` imports that module and proves six additional theorems:

- `singular_type1_cylinder` and `singular_type3_cylinder`: the exact branch
  equations and oddness of the returned cofactors force the source cylinders
  `u=1+32*k, u'=1+30*k` and `u=1+128*k, u'=1+102*k`, respectively.
- `singular_type1_next_excess` and `singular_type3_next_excess`: certify the
  next first-step excesses `5+135*k` and `19+1683*k`.
- `singular_type1_terminal_equation` and `singular_type3_terminal_equation`:
  certify the exact Diophantine equations obeyed by any immediate terminal
  successor.

The classification that these are the only zero-residual triples is the
result in the Agent 16 dossier; this file formalizes the source cylinders and
their immediate successors conditional on those triples.

The source theorem is not merely an algebraic restatement: it invokes
`SheepEven.Step.generic`, `SheepEven.even_successor`, and
`SheepEven.factor_odd`. The residual identity is therefore connected to the
actual Sheep even-return dynamics, rather than only to an abstract recurrence.

`GenericResidual.lean` and `SingularCylinders.lean` contain ten source and
singular-branch theorems. `ThreeAdicLTE.lean` adds the formal three-adic
exponent-divisibility theorem and the H >= 9 lower bound. Their `#print axioms`
reports contain only the standard `propext` and `Quot.sound`; there is no
`sorryAx`.

## New consequence: exact two-step barriers after the two singular edges

The weighted-cofactor analysis in the Agent 16 dossier identifies exactly two
zero-residual branch triples:

- Type I: `(a,h,b) = (1,1,2)`
- Type II: `(a,h,b) = (3,1,4)`

For their genuine source families, write respectively:

```text
Type I:  u = 1 + 32*k,   k >= 1
Type II: u = 1 + 128*k,  k >= 1
```

After the singular edge, the next even source and its next first-step excess are
exactly:

| First singular edge | Next even source | Next `F(x_next)-1` |
|---|---:|---:|
| `(1,1,2)` | `4*(1+30*k)` | `5+135*k` |
| `(3,1,4)` | `16*(1+102*k)` | `19+1683*k` |

Let `H = v2(F(x_next)-1)` on that next source. If its following even-return
output is a power of two `2^B`, then the exact terminal equations are:

```text
Type I:  3^H*(5+135*k)    = 2^H*(2^B-1)
Type II: 3^H*(19+1683*k)  = 2^H*(2^B-1)
```

**Sharp lower bounds:**

- After `(1,1,2)`, any two-step terminal output has `B >= 32`.
  Equality occurs at `H=1`, `B=32`, `k=21,209,715`.
- After `(3,1,4)`, any two-step terminal output has `B >= 11,502`.
  Equality occurs at `H=5`, `B=11,502`, with

  ```text
  k = (2^5*(2^11502-1)/3^5 - 19)/1683
  ```

  an integer with 3,459 decimal digits.

### Proof of the bounds

For every `H >= 1`, the LTE identity

```text
v3(4^n-1) = 1 + v3(n), for n >= 1
```

implies

```text
3^H | (2^B-1)  ==>  2*3^(H-1) | B.
```

The Lean file `ThreeAdicLTE.lean` formally proves the divisibility implication
used here, namely `3^H | (4^n-1) ==> 3^(H-1) | n`, then derives
`3^H | (2^B-1) ==> 2*3^(H-1) | B`. It also formally proves the H >= 9
consequence `B >= 13122` for B >= 1. A short proof of the full LTE identity is obtained from
`4^n = (1+3)^n = 1+3*n (mod 9)` and

```text
4^(3*m)-1 = (4^m-1)*(4^(2*m)+4^m+1),
```

where the second factor is exactly `3 (mod 9)`. Iterating the factorization
removes one factor of `3` from the exponent and one from the valuation.

For the `(1,1,2)` family, `H=0` is impossible modulo `3`. For `H>=3`,
`B` is divisible by both `4` (modulo `5`) and `2*3^(H-1)`, hence
`B >= 4*3^(H-1) >= 36`. The two remaining cases reduce to:

- `H=1`: `2*(2^B-1) = 15 (mod 405)`, whose solutions are
  `B = 32 (mod 108)`;
- `H=2`: `4*(2^B-1) = 45 (mod 1215)`, whose solutions are
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

Restore the source module from the Agent 16 dossier, then compile these files:

```sh
# Run from the repository root.
python3 im-results/agent16-sheep-even-return/reconstruct.py
LEAN_PATH=im-results/agent16-sheep-even-return lean -o im-results/agent16-sheep-even-return/SheepEven.olean im-results/agent16-sheep-even-return/SheepEven.lean
LEAN_PATH=im-results/agent16-sheep-even-return lean -o im-results/agent14-sheep-weighted-residual/GenericResidual.olean im-results/agent14-sheep-weighted-residual/GenericResidual.lean
LEAN_PATH=im-results/agent14-sheep-weighted-residual:im-results/agent16-sheep-even-return lean im-results/agent14-sheep-weighted-residual/SingularCylinders.lean
LEAN_PATH=im-results/agent14-sheep-weighted-residual lean im-results/agent14-sheep-weighted-residual/ThreeAdicLTE.lean
python3 im-results/agent14-sheep-weighted-residual/check_singular_two_step.py
```

The Lean files were compiled with Lean 4.36.0-rc2. The Python script uses only
the standard library and verifies the finite modular tables and the two sharp
witnesses.

## Scope and limitation

These results strengthen the exact arithmetic description of the two
zero-residual branches and provide a source-connected formalization of the
weighted identity, the two singular source cylinders, and the exact equations
for an immediate terminal successor. They do **not** show that the blank-root
trajectory enters one of these branches, that it avoids them, or that the Sheep
machine halts or runs forever. In particular, the barriers apply only when a
zero-residual edge is followed immediately by a terminal edge; they do not
exclude a later terminal edge after additional generic returns.

# Branch-9 diagonal feeder: exact reduction to a blank-root zero state

**Status:** intermediate. The algebraic identities are exact; the inverse-tree sweep is exploratory computation, not a Lean-certified theorem. No BB(6) or full #429 decision is claimed.

## Last-reset equation and inverse grammar

For the branch-9 pre-reset state `(x,y)`, burst length `n), and reset parameter `d),

```
4*x = 2^(n+2)*(d+10) + 2*d - 3*n - 25
y   = 2*(x-d)+1.
```

Let `h=(2*d-3*n-13)/4). Then `x=2^n*(d+10)+h-3).

The inverse parents used in the exact DFS are:

```
F⁻¹(a,b) = ((a-3)/2, a+b)                    [a odd]
S⁻¹(a,b) = ((4*a+b-26)/4, (b+4)/2)          [a odd, b%4=2]
E⁻¹(a,b) = ((4*a+b-14)/4, b/2)              [a even, b%4=2].
```

At an odd state with `b%4=2`, both F and S must be explored. Following F alone is not automatically justified.

## Diagonal h=0 feeder

On `h=0), `d=(3*n+13)/2` and `x=2^n*(d+10)-3`. Along the all-F inverse spine, for `0≤i≤n`,

```
a_i = 2^(n-i)*(d+10)-3
b_i = (2^(i+1)-1)*2^(n-i+1)*(d+10) - 2*d - 5 - 3*i.
```

Thus `(a_n,b_n)=(d+7, 2^(n+2)*(d+10)-4*d-25-3*n)`.

Set `d+7=12*2^J-3`. This gives the subfamily

```
n = 8*2^J-11
d = 12*2^J-10.
```

After J more F inverses, the all-F path reaches `(9,b_J)), where `b_J=b_n+24*2^J-24-3*J`. Two forward first-branch steps from `(0,z_J)` reach `(9,b_J)), with

```
z_J = b_J+12
    = 12*2^(n+J+2) - 48*2^J + 36 - 3*J.
```

The private `nine_predecessor` lemma in `im-results/agent39-429-1021/BB429RootMod64R2.lean` gives the unique predecessor `(3,b+9)` of `(9,b)`; direct source case analysis gives the unique predecessor `(0,b+12)` of a state with first coordinate 3. Therefore, **if** all S alternatives along this spine are excluded, the remaining question is exactly whether `(0,z_J)` is blank-root reachable. Conversely, a root visit to `(0,z_J)` deterministically generates the feeder and the branch-9 prestate.

## Exact-integer inverse-tree exploration

A DFS over exact BigInt states explored F and S at odd states (S when `b%4=2`) and E at even states (when `b%4=2`), deduplicating states. Leaves were tested against a selected set of current repository invariants: `BB429Mod8.Allowed`, positive-even mod-8/mod-16 rows, root mod-16/mod-32 strong rows, odd/odd rows from the branch-9 work, and Agent 39 forbidden cells `no_15_26`, `no_15_24`, `no_31_24`, `no_1_25`, `no_1_23`, `no_33_23`, `no_5_20`, `no_3_18`, `no_9_9`, `no_21_20`.

| J | n | d | unique states | low leaf | low-leaf b mod 64 | z_J mod 128 |
|---:|---:|---:|---:|---|---:|---:|
| 2 | 21 | 38 | 45 | (9,b) | 18 | 94 |
| 3 | 53 | 86 | 89 | none | — | 27 |
| 4 | 117 | 182 | 183 | (9,b) | 12 | 24 |
| 5 | 245 | 374 | 353 | none | — | 21 |
| 6 | 501 | 758 | 739 | (9,b) | 6 | 18 |
| 7 | 1013 | 1526 | 1488 | none | — | 15 |
| 8 | 2037 | 3062 | 2987 | (9,b) | 0 | 12 |

For J=3,5,7 all explored branches close under the selected invariants. For J=2,4,6,8 the only surviving leaf is the all-F path to first counter 9. This is finite computational evidence only; no uniform proof in J has been established.

Every transition with output first coordinate 0 has even second coordinate. The existing `rooted_zero_two_gateway_sharp` theorem in `im-results/agent18-429-root-invariants/BB429OddResetGate.lean` says a root state `(0,z)` with `z%4=2` must have either:
- high-two source `(u,2*u+2)`, `u%16 ∈ {0,4,5,8,9,12,13}`; or
- odd-reset source `(u,2*u-3)`, `u%32 ∈ {7,13,15,21,29,31}`.

For J=2, `z_J%128=94`: the two source residues are `(z_J-18)/4=19 (mod 32)` and `(z_J-2)/4=23 (mod 32)`; both fail the gateway. Subject to formalizing the finite inverse tree, this closes the J=2 member.

For J=6, `z_J%128=18`: the high-two source has `u=0 (mod 32)`, while the odd-reset source has `u=4 (mod 32)`. The odd-reset alternative fails, but the high-two source survives. This is a direct target for Agent 32's high-two/Junc work.

For J=4 and J=8, `z_J%4=0`, so the zero-two gateway does not apply. A useful next theorem is a source classification for root states `(0,z)` with `z%4=0`. The broad source cases are `w=2*u`, `d=1,w=2*u-2`, or even `w` with odd `d=u-w/2≥3`; the last family remains too broad under current residue rows.

## General non-diagonal branch-local formula

For `h!=0`, let `r=v₂(h)` and `H=h/2^r` (odd). Along the F-only branch, for `r<n`,

```
a_r = 2^(n-r)*(d+10)+H-3
b_r = (2^(r+1)-1)*(2^(n-r+1)*(d+10)+2*H)-2*d-5-3*r.
```

When `r≤n-2`, the large power term vanishes mod 8. If this F-ancestor is the actual root ancestor, it is positive even, so `b_r%8=2` is required. This yields:
- `d%4=2`: for r=1, H%4=1; for r≥2, either (H%4=1 and r%8=1) or (H%4=3 and r%8=5).
- `d%4=0`: for r=1, H%4=3; for r≥2, either (H%4=1 and r%8=5) or (H%4=3 and r%8=1).

These are branch-local constraints, not global necessary conditions until the alternative S parents are handled.

## Next proof obligations

1. Formalize the J=2 inverse tree and combine it with the existing zero-two gateway.
2. Prove a uniform modular description of the S side branches along the diagonal spine.
3. Coordinate J=6 with Agent 32's high-two/Junc work.
4. Derive a zero-state `z%4=0` predecessor gateway for J=4,8 and later J.
5. Extend the valuation filter to a complete two-parent inverse-tree argument.

This is intermediate work; nothing belongs in `results/` yet.

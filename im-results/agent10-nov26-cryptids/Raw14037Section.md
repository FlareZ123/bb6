# Raw140 sibling cluster 37/40/44/83: shared section return

Status: **intermediate; M37 formal CI pending**.  This file records the reproducible
section structure and the exact theorem currently emitted by
`generate_raw140_37_section.py`.

## Machines

The clustered three-hole residual completions are:

- 37: `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RE---`
- 40: `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1LC---`
- 44: `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RC---`
- 83: `1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1LE---`

All four are still live far beyond the shallow finite filters.  Block simulation
from blank reaches the same sequence of section states; only the primitive entry
cost differs by a small constant.

Write
`S(a,p,n,r)` for the boundary state

```
q = B, direction = left
left  = 1^a 3^p 5^n
right = 2^r 1 5
```

with block symbols in nearest-first order.  The first shared section hits are:

| sibling | blank cost to S(2,5,29,1) | next | deep next |
|---:|---:|---|---|
| 37 | 6412 | S(3,13,23,1) at 8171 | S(2,134,410,1) at 1,494,142 |
| 40 | 6416 | S(3,13,23,1) at 8175 | S(2,134,410,1) at 1,494,158 |
| 44 | 6410 | S(3,13,23,1) at 8169 | S(2,134,410,1) at 1,494,134 |
| 83 | 6414 | S(3,13,23,1) at 8173 | S(2,134,410,1) at 1,494,150 |

The clean half-return is independent of the six-block tail count:

```
S(2,p,n,1) -> S(3,p+8,n-6,1)      (n >= 6)
primitive cost = 132*p + 1099
```

The M37 generator proves a stronger tail-parametric form.  If `X` is any
block-list tail,

```
B-left [1,1,3^p,5,5,5,5,5,5]++X ; [2,1,5]
  --(132*p+1099)-->
B-left [1,1,1,3^(p+8)]++X ; [2,1,5].
```

The 136-chunk symbolic derivation contains a reusable common-table primitive

```
E-left [1]++X ; [5,1]++Y
  --19-->
E-left [1,3]++X ; [5]++Y,
```

and its induction over an arbitrary run of right-side 1-blocks.  Direct
block-exit comparison shows every ordinary source exit used by the M37
derivation has the same exit tuple for siblings 40, 44, and 83.  Therefore the
same symbolic theorem is expected to transfer to all four tables after M37
acceptance; this is a finite proof-generation task, not a dynamical conjecture.

The hard half-return `S(3,13,23,1) -> S(2,134,410,1)` uses 514,903 macro
exits for sibling 37 (1,485,971 primitive steps).  Its compressed trace contains
139 instances of the same 19-step primitive plus long affine sweeps.  The next
mathematical target is to factor that half-return into a small arithmetic
transition system and prove its recurrence, which would attack four residual
cylinders at once.

Reproduction: the formal source generator is
`im-results/agent10-nov26-cryptids/generate_raw140_37_section.py`;
workflow target `section37` in `.github/workflows/agent10-raw140-seven.yml`
compiles and axiom-audits `Raw14037Section.behindMany` and
`Raw14037Section.section23`.

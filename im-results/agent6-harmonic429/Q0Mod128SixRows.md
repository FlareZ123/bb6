# Six q0 root-inverse sectors on the line b = 2a - 13

**Status: derived candidate; not yet compiled against the repository's full Lean dependency closure.** This is an intermediate result, not a claim that the q0 family is closed.

## Claim to formalize

For the #429 accelerated blank-root reachability predicate `BB429NewResidue.Reach`, the following appears to follow from the established inverse equations, `BB429Mod8.Allowed`, and `BB429RootEven8.rooted_positive_even_eight`:

```text
a >= 1,000,000 and a mod 128 in {5, 53, 69, 85, 101, 117}
    implies not Reach(a, 2*a - 13).
```

The six residues correspond to these q0 sectors. With `n = 23 + 32*u`, `a = 13*2^n - 24*u - 19`, and `b = 2*a - 13`, we have `a mod 128 = (-24*u - 19) mod 128`, since `n >= 23`:

| `u mod 16` | `a mod 128` |
|---:|---:|
| 1 | 85 |
| 5 | 117 |
| 7 | 69 |
| 11 | 101 |
| 13 | 53 |
| 15 | 5 |

Thus six entire infinite subfamilies of the outstanding `(n mod 32, d mod 16) = (23, 7)` class are candidates for exclusion. Ten residue classes of `u mod 16` remain untouched by this argument.

## Exact inverse tree

Start at `P0 = (a,b) = (a,2*a-13)`. All six `a mod 128` values are `5 mod 16`, so `a` is odd and `b mod 4 = 1`. The first inverse is forced to be F:

```text
P1 = ((a-3)/2, 3*a-13)
```

Here the first coordinate is odd and the second is `2 mod 4`, so the inverse splits into F and S:

```text
P2F = ((a-9)/4, (7*a-29)/2)
P2S = ((5*a-45)/4, (3*a-9)/2)
```

Both are odd with second coordinate `3 mod 4`, hence each has only an F predecessor:

```text
P3F = ((a-21)/8, (15*a-67)/4)
P3S = ((5*a-57)/8, (11*a-63)/4)
```

Both first coordinates are positive even numbers. Their second-coordinate residues are:

| `a mod 128` | `P3F.second mod 8` | `P3S.second mod 8` |
|---:|---:|---:|
| 5 | 2 | 6 |
| 53 | 6 | 2 |
| 69 | 2 | 6 |
| 85 | 6 | 2 |
| 101 | 2 | 6 |
| 117 | 6 | 2 |

Every row therefore has exactly one child immediately excluded by the positive-even-eight root invariant (the second coordinate must be `2 mod 8`). The other child has a unique E inverse. Its coordinates simplify to:

- E after `P3F`: `P4F = ((17*a-165)/16, (15*a-67)/8)`.
- E after `P3S`: `P4S = ((21*a-233)/16, (11*a-63)/8)`.

The surviving E-parent residues and their closure are:

| `a mod 128` | surviving branch | `P4 mod 8` | final obstruction |
|---:|:---:|:---:|---|
| 5 | F | (3,1) | Its forced F child is positive even with second coordinate `4 mod 8`. |
| 53 | S | (7,1) | Violates `Allowed` directly: `a mod 8 = 7` requires second coordinate `2 or 3 mod 4`. |
| 69 | F | (7,1) | Same direct `Allowed` contradiction. |
| 85 | S | (1,5) | Forced F reaches an odd split state `(3,6) mod 8`; both F and S children are positive even with second coordinate `1 mod 4`, contradicting the positive-even-eight invariant. |
| 101 | F | (1,5) | Same `(3,6) mod 8` split and positive-even contradiction. |
| 117 | S | (3,1) | Its forced F child is positive even with second coordinate `4 mod 8`. |

The two reusable terminal checks are elementary:

1. From an odd state `(r,s)` with `(r,s) = (3,1) mod 8`, the forced F predecessor has even first coordinate and second coordinate `4 mod 8`, so it cannot be a blank-root state.
2. From an odd state with `(r,s) = (1,5) mod 8`, the forced F predecessor is odd and `(3,6) mod 8`. Its F child is even with second coordinate `1 mod 4`; its S child is even with second coordinate `1 mod 4`. Both violate the positive-even-eight invariant.

All states used in this finite tree remain above the inverse-lemma thresholds when `a >= 1,000,000`. For the q0 family, that lower bound follows from `n = 23 + 32*u` and `u >= 0`.

## What is and is not established

- The arithmetic tree above is a proposed exact proof from the existing inverse and root-invariant lemmas; it is not a numerical simulation.
- The q0 subfamily `u mod 16 = 7` has a proof-body check against declaration stubs matching the repository theorem signatures. This does not establish the generic line lemma or the other five sectors.
- The full source dependency closure has **not** been compiled locally, so no Lean source certificate or CI claim is made here.
- This does **not** close the q0 family. The ten remaining `u mod 16` sectors require separate treatment, including the unbounded FSFE valuation branch.

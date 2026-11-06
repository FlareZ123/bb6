# Exact finite-q dyadic shadow closure: intermediate frontier data

**Agent 9, 2026-11-05 to 2026-11-06.** This dossier records exact finite-q shadow graph computations. A shadow closure alone is not an authentic P1 `Reach` exclusion; three cases below have since been lifted through the unchanged original source relation. The remaining rows are computational candidates only. This technical data and its generators stay in `im-results/` by design.

## What is computed

For a fixed integer `q`, set source feeder `h=8` or `9`, `L=16q+h`, and root `(m,z)=(0,12q+4)` for h=8 and `(0,10q+4)` for h=9. Construct the complete finite closure of every possible dyadic shadow transition

```text
z = 2^t * v,
2*z' + 1 = L + m + t + v,
m' = m+t+1
```

over all nonnegative `t` for which `2^t∣z` and the required parity makes `z'` integral. The exact integer BFS in [exact_fixed_shadow.py](./exact_fixed_shadow.py) computes the entire closure until its queue is empty. Cases exceeding a 1-million node safety ceiling are explicitly marked incomplete rather than reported as closed; the cases below did not hit the ceiling.

| q | Feeder h=8 nodes | Feeder h=9 nodes | Max cost m (h=8 / h=9) | Max 2-adic valuation of z (h=8 / h=9) |
|---:|---:|---:|---|---|
| 1 | 24 | 26 | 10 / 10 | 4 / 4 |
| 2 | 77 | 69 | 27 / 26 | 5 / 5 |
| 6 | 30 | 20 | 11 / 10 | 4 / 6 |
| 26 | 14 | 12 | 11 / 9 | 3 / 4 |
| 29 | 12 | 14 | 10 / 10 | 5 / 4 |
| 33 | 118 | 116 | 41 / 40 | 7 / 9 |
| 37 | 3927 | 3823 | 250 / 250 | 9 / 9 |
| 41 | 49 | 41 | 25 / 24 | 4 / 7 |
| 45 | 4804 | 4726 | 401 / 400 | 9 / 10 |
| 53 | 44 | 46 | 19 / 17 | 7 / 9 |
| 65 | 51 | 35 | 19 / 17 | 5 / 7 |
| 70 | 195 | 199 | 57 / 56 | 6 / 6 |
| 89 | 258 | 280 | 51 / 50 | 10 / 7 |
| 101 | 29882 | 29856 | 769 / 768 | 11 / 11 |
| 113 | 2348 | 2410 | 227 / 226 | 10 / 10 |

## Source-lifted fixed-q cases

Three of the high-cost finite shadows have now been lifted to the original P1 `Reach` relation by the arbitrary-`K`, arbitrary-budget source bridge in [the q-base cylinder dossier](../agent9-p1-q41/README.md):

| q0 | K | B | Source-certified family | CI |
|---:|---:|---:|---|---|
| 37 | 10 | 250 | `q=37+2^260 r`, `n=594+2^264 r` | [42258300305](https://github.com/FlareZ123/bb6/actions/runs/42258300305) |
| 70 | 10 | 57 | `q=70+2^67 r`, `n=1122+2^71 r` | [42253385501](https://github.com/FlareZ123/bb6/actions/runs/42253385501) |
| 89 | 11 | 51 | `q=89+2^62 r`, `n=1426+2^66 r` | [42253385501](https://github.com/FlareZ123/bb6/actions/runs/42253385501) |

Each statement excludes only the necessary original-source critical gateway `BB6.Agent1.Reach 2 (H(16q+2))` throughout the indicated infinite q cylinder. None decides the P1 machine or establishes a BB(6) bound.

The q37 graph required a scalable kernel certificate. [QBudgetRows.lean](./QBudgetRows.lean) checks one cost row at a time: each row's z values are verified against all t<K, and every valid successor is required to lie in the next row. The 251 row theorems per feeder are individually reduced by `decide`; a nested case proof assembles them into a uniform row-check theorem. The predicate-based source bridge then lifts the two closed invariants without a global linear List-membership reduction. [generate_q37_rows.py](./generate_q37_rows.py) deterministically regenerates the data and proof modules.

## Remaining shadow-only candidates

The other rows in the census remain finite computational candidates. In particular, q45 needs B=401, q101 needs B=769, and q113 needs B=227; no original-source lift is claimed here. The earlier list-based global checker was too expensive for q37, and the row-grouped certificate is the currently validated route for larger graphs. Future work should prioritize the remaining source exits and budget inequalities, while checking prior exact source families before claiming new coverage.

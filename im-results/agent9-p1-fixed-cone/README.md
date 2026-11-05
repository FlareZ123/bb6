# Exact finite-q dyadic shadow closure: intermediate frontier data

**Agent 9, 2026-11-05.** Purely *shadow-graph* computations, **not** authentic P1 `Reach` exclusions or machine-halting decisions. Use these as candidate finite inverse certificates for source-level proof. This dossier stays in `im-results/` by design.

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

Every finite closure shown is a **computational mathematical candidate only**. It does not demonstrate that the original predecessor cone is finite with source verification, nor does it rule out positive-even right-counter exits, exceptional `c=1`, or original blank-root reachability. Source lifting via [Agent 9's budget-parametric core](../agent9-param-budget/ShadowFiniteBudgetK.lean) requires the exact two-feeder encoding, proper exponent gap `budget+K+3≤N`, source terminal obstructions, and a credible width inequality.

## Strategic implication

Several still-uncovered indices have complete *fixed-q* finite shadows but cumulative costs much greater than the m≤12 criterion used for parametric q modulo1024. For example, q33 requires m≤41 and at most 9 binary factors for its right-coordinate z, while q37 needs m≤250 and at most 9. These may be approachable with specialized source-certified inequalities using the genuine lower bound `2^(16q)`, rather than the weaker global linear lower bound `2^(16q)≥65536q` used for q≥29 and small cost. The extra work is to prove original terminal barriers, and kernel-check thousands of finite graph edges efficiently (potentially by `decide`/reflection).

This numerical census is **not new BB(6) progress until one of those cases is lifted through unmodified original source and every predecessor exit is discharged**. The source-certified infinite-class result and 700/1024 density remain in [the proper academic synthesis](../../results/2026-11-05-p1-700-source-gateway-density-agent9.md). Future agents should check prior fixed-index source results before claiming a new excluded value.

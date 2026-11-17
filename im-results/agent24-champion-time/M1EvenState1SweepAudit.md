# M1-even state-1 sweep: precondition audit and next root gap

**Status:** exact finite-source simulation and arithmetic diagnosis; not a Lean proof and not a BB(6) result.

## 1. The local three-step lemma is sound, but its proposed placement is not uniform in a

Agent 48's `state1_three_left` / `counted_left_sweep_from1` is a valid local source macro: `n` three-step cycles require `n+1` consecutive ones immediately to the left of the blank under the state-1 head.

The proposed M1-even decomposition in `M1EvenZeroValuationGap.md` applies `4(v₂(n)-1)` such cycles immediately after a `12a+6`-step prefix. For `v₂(n)=5), this requires 16 cycles and hence 17 consecutive ones. That premise is not uniform in the S1 unary parameter `a`.

Using the exact `tm2` transition table from `ChampionRootBridge.lean` and the exact `S1Encoder` block order, with `L=16,n=32,m=1,b=0`, the following are the configurations after `12a+6` steps:

| a | state | head (initial head 0) | blank under head? | consecutive ones to left | required |
|---:|---:|---:|:---:|---:|---:|
| 1 | 1 | -4 | yes | 19 | 17 |
| 3 | 1 | -12 | yes | 17 | 17 |
| 5 | 1 | -20 | yes | 15 | 17 |
| 10 | 1 | -40 | yes | 10 | 17 |
| 20 | 2 | -82 | yes | — | 17 |

Thus at `a=10`, the `state1LeftOnes` premise for `counted_left_sweep_from1 16` is false; at `a=20`, even the claimed state-1 prefix endpoint is false. The 12-step hole-shift lemma itself is unaffected. What fails is the asserted *uniform source-tape precondition* for applying 16 cycles after that prefix.

The script `M1EvenState1SweepAudit.mjs` reproduces the table from the exact transition table and S1 encoding. The tested full prefix of length `12a+12v₂(n)+32` still reaches state 4 at head `h+4` for the sampled cases, so this audit does **not** refute the proposed total cost or source theorem. It refutes only the current fixed-sweep decomposition as a proof for arbitrary `a`. A correct proof needs an `a)-dependent phase split or a different invariant; do not claim the fixed 16-cycle sweep is available for the authentic root parameter.

## 2. The full middle itinerary also needs the M1-even valuation-four row

Let `R = tm63RootResidueSixK`, known odd. After middle row 26 and the five rows listed in `M1EvenZeroValuationGap.md`, the marker-1 index is
[
n_0=16R-16.
]
Every 24 source decrements return to marker 1, so the subsequent marker-1 indices are
[
n_j=16R-16-24j=8(2R-2-3j).
]

Their 2-adic valuations are forced by parity alone:

- If `j` is odd, `2R-2-3j` is odd, so `v₂(n_j)=3`.
- If `j=2u` with `u` odd, `n_j=16(R-1-3u)` with odd factor, so `v₂(n_j)=4).
- If `j=2u` with `u` even, `R-1-3u` is even, so `v₂(n_j)≥5`.

The existing `m1ZeroOdd_residue0_counted_increment_source` covers the valuation-3 class. Agent 48's proposed `n=32q` family covers valuation at least 5. A complete middle section therefore also needs a counted M1-even source theorem for
[
m=1,qquad n=16q,qquad q	ext{ odd},
]
with exact proposed cost
[
6cdot4^b+42cdot2^b+67+12a-9b.
]
This valuation-four row recurs every other 24-cycle (when `u` is odd); it is not optional after closing the first `n=32q` instance.

## Recommended next proof target

First replace the unsupported fixed `4(v₂(n)-1)`-cycle placement with a phase decomposition that is valid for arbitrary `a). In parallel, add the explicit `m=1,n=16q` odd-quotient row to the 24-cycle source-coverage plan. Keep both items in `im-results/` until the exact original-source Lean proof compiles and its transitive axiom profile is clean.

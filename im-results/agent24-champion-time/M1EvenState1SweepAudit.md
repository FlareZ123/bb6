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


## 3. Correct valuation-bridge placement found after the counted left sweep

The failed placement above was not the right place to use the state-1 macro. A much cleaner bridge appears **after** the existing `counted_left_sweep (3*a+1)` from `M1EvenQ4Prefix.lean`. That sweep costs `9*a+3` and leaves state 3 at `hN = h-(3*a+1)`. Let `v=v₂(n)≥1`, with n's exact low-bit factorization `n=2^v*q`, q odd.

The bridge from state 3 at `hN` has the following phase decomposition:

1. A fixed 6-step prelude reaches state 1 at `hN`, blank under the head. The exact S1 source word supplies `3*v+4` consecutive ones to the left. This is exactly the premise for `counted_left_sweep_from1 (3*(v+1))`.
2. The state-1 left sweep uses `3*(v+1)` three-step cycles: `9*(v+1)` steps, moving the blank to `hN-3*(v+1)`.
3. A fixed 4-step exit reaches state 4 at `H = hN-3*(v+1)-2`, blank under the head.
4. A fixed 3-step prelude reaches state 5 at `H+3`.
5. The left sweep has written exactly `3*(v+1)` consecutive ones immediately to the right of `H+3`. A rightward state-5 sweep of `v+1` three-step cycles consumes them and returns state 5 at `hN+1`, reading blank.
6. One fixed step exits state 5 to state 4 at `hN+2`; the three source ones at `hN+2,hN+3,hN+4` then give a final 3-step state-4 scan to `hN+5`.

The total bridge cost is
\[
6+9(v+1)+4+3+3(v+1)+1+3=12v+29.
\]
Composing with the initial `9a+3` left sweep and the final `3a` state-4 scan from `hN+5) to `h+4) gives the uniform M1-even q4 prefix cost
\[
(9a+3)+(12v+29)+3a=12a+12v+32.
\]
Adding the existing q4 suffix gives exactly `proposedIncrementCost 1 n a b`, namely `6*4^b+42*2^b+19+12*a+12*v-9*b`.

This is stronger than a separate v2=4 patch: one source theorem for arbitrary exact valuation v covers both the missing `n=16q` (q odd) row and the proposed `n=32q` (and higher) rows. It also recovers the existing v=1 bridge length 41. Finite simulations for n=6,16,32,64,96,128 and a=1 confirm every phase endpoint and exact length. The proof obligations still to formalize are:

- a `state5_three_right` lemma and its counted `v+1)-cycle iterator (the symmetric rightward macro);
- the `binDec`/S1-source proof of the initial `state1LeftOnes` length `3v+4`;
- the fixed 6-, 4-, 3-, and 1-step phase transitions and the final 3-cell q4 scan;
- the fact that the left-sweep output supplies the right-sweep ones, and the final source window supplies the last three q4 ones.

This phase decomposition replaces the unsupported fixed `4(v₂-1))-cycle placement after `12a+6`. The local left-sweep macro remains useful, but its correct use is after the counted left sweep at `hN`.


## 4. Exact state-1-to-state-4 bridge contract

The variable part can be isolated from the 6-step prelude. Put `N=3*(v+1)`. For an arbitrary tape `T) and head `h`, the bridge theorem should take these hypotheses:

- `T h = false`;
- `state1LeftOnes T h (N+1)` (equivalently `3*v+4` consecutive ones immediately left of h);
- `T (h-N-2) = false` and `T (h-N-3) = false` (the first two zeros of the `d0` block beyond those ones);
- `T (h+1) = false` and `T (h+2)=T(h+3)=T(h+4)=true` (the four-cell [false,true,true,true] boundary left by the initial counted sweep).

Then the `12*v+23)-step run from `⟨1,h,T⟩` decomposes as follows:

| Phase | Exact run | Endpoint |
|---|---:|---|
| left-hole sweep | `3*N = 9(v+1)` | state 1 at `h-N`, blank |
| four-step left exit | 4 | state 4 at `H=h-N-2`, blank |
| rightward setup | 3 | state 5 at `H+3=h-N+1` |
| right-hole sweep | `3(v+1)=N` | state 5 at `h+1`, blank |
| state-5 exit | 1 | state 4 at `h+2` |
| final q4 scan | 3 | state 4 at `h+5` |

The left sweep's output tape `state1SweptLeft N T h` has a blank at `h-N` and writes ones at every cell `h-N+1,...,h`. These are exactly the `N=3(v+1)` cells consumed by the state-5 right sweep. The extra `(N+1)`st left one plus the two zeros beyond it give the four-step exit. The right sweep does not touch `h+1`, so its blank survives to the one-step state-5 exit; the final q4 scan then uses the untouched three ones at `h+2,h+3,h+4`.

The output tape is the composition of these three simple updates: `state1SweptLeft N T h`, the fixed four-step exit writes at `h-N,h-N-1,h-N-3`, the fixed three-step setup writes at `H,H+1,H+2`, then `state5SweptRight (v+1)` from `h-N+1`, then the one-step state-5 exit writes at `h+1`. The final q4 scan leaves the tape unchanged. This contract is independent of the quotient q except for the two-zero boundary supplied by the first `d0` block after `d1pow v`.

This is the clean theorem interface for a Lean implementation. The new `M1EvenState5Sweep.lean` supplies the rightward iterator; Agent48's existing `M1EvenState1Sweep.lean` supplies the leftward iterator. The remaining work is only the finite transition lemmas and the S1 source-shape proof for the six-step prelude.


## 5. The six-step prelude hypotheses follow directly from S1Encoder

Let `T0 = sweptLeft (3*a+1) (s1Config L n 1 a 0 b h).tape h` and `hN=h-(3a+1)`, the endpoint of the existing `counted_left_sweep`. The head-facing source suffix to the left of hN is
```
markerWord 1 ++ d0 ++ binDec L n ++ lh
```
(as in `m1EvenSourceLeftAt` in `M1EvenQ4Prefix.lean`). Since `markerWord 1=[true,false,true]` and `d0=[false,false,true]`, the four cells read by the fixed six-step prelude are
```
T0(hN)=false, T0(hN-1)=true, T0(hN-2)=false, T0(hN-3)=false.
```
The exact six-step trace is
```
state 3 @ hN  --false--> state 2 @ hN-1
state 2 @ hN-1 --true-->  state 3 @ hN-2
state 3 @ hN-2 --false--> state 2 @ hN-3
state 2 @ hN-3 --false--> state 4 @ hN-2
state 4 @ hN-2 --false--> state 0 @ hN-1
state 0 @ hN-1 --false--> state 1 @ hN
```
It leaves the head blank and writes ones at hN-1,hN-2,hN-3. The third bit of the preceding `d0` block supplies one more one at hN-4.

For exact `v=v₂(n)`, write `n=(2q+1)2^v` with q odd. S1Encoder's existing `binDec_carryPrefix` gives
```
binDec L n = d1pow v ++ d0 ++ binDec (L-v-1) q.
```
The `d1pow v` block contributes 3v ones immediately after hN-4. Therefore after the six-step prelude the left side has exactly the required `3v+4` consecutive ones; the next two cells are the first two false bits of the following `d0) block, giving the two exit zeros at hN-(3v+5) and hN-(3v+6).

The right-side hypotheses are not from the original S0 right-facing suffix. They are the local boundary left by the *first* `counted_left_sweep`: `sweptLeft_plus1` gives a blank at hN+1, and `sweptLeft_block` gives ones at hN+2,hN+3,hN+4. The six-step prelude does not touch these cells. This is exactly the right-side input needed by the generic bridge contract in section 4.

Thus all source-shape hypotheses for the generic bridge reduce to existing `sweptLeft` lemmas plus `binDec_carryPrefix`; no simulation-specific tape assumption is needed. The remaining new proof code is the fixed six-step run, the fixed four-/three-/one-step transitions, and the composition with the two counted sweeps.


## 6. Consequence for the full 24-cycle root itinerary

The exact-valuation bridge is needed only for `v₂(n)≥4` in the root's marker-1 `n≡0 mod 8` rows. The existing `m1ZeroOdd_residue0_counted_increment_source` handles the exact `v₂(n)=3` class. For `n_j=16R-16-24j` with R odd:

- odd j gives `v₂(n_j)=3`;
- even j gives `v₂(n_j)≥4` (with exact valuation 4 when j/2 is odd, and at least 5 when j/2 is even).

Therefore, **if the generic M1-even valuation bridge is formalized and composed with the existing q4 suffix**, it and the existing M1-zero-odd theorem cover every marker-1 row in the complete 24-cycle middle itinerary. The separate v4/v5 source modules are unnecessary; one exact-v theorem for v≥4 is the cleaner target. The remaining root work is the formal 24-cycle induction and its connection to the authentic middle-26 endpoint, not another valuation split.

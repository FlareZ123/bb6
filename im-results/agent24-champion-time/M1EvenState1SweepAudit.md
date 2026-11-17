# M1 state-1 sweep and valuation-parametric source audit

**Status — 17 November 2026.** The generic M1 valuation-parametric counted-increment source theorem is now written in `im-results/agent48-counted-inc0/M1EvenValuationSource.lean`, namespace `BB6Coverage.Agent48M1EvenValuationCountedSource`. Manual mathematical/API review found no substantive mismatch in the bridge, q4 cut, right-shape/far-tail, or final drain composition. The theorem remains **uncompiled**; its `#print axioms` commands are present but have not been executed in an accepted dependency closure.

## 1. Current all-index source theorem

The public theorem is:

~~~lean
m1EvenValuation_counted_increment_source
  (L n a b : Nat) (h : Int)
  (hn : 0<n) (hnlt : n<2^L) (ha : 0<a) :
  run tm2 (proposedIncrementCost 1 n a b)
    (s1Config L n 1 a 0 b h) =
  some (s1Config L (n-1) 0 (a+b+2) 0 (2^b-1)
    (h+5+(3*b:Int)))
~~~

It handles every positive `n<2^L`, including exact valuation `v₂(n)=0`; it is stronger than the original all-even target. The proof factorizes `n=(2*q+1)*2^v` with `exists_odd_factor_bounded L n hn hnlt`, proves the factorized source theorem, then rewrites by the factorization. Thus the root's marker-1 rows no longer need a separate split into valuations 3, 4, and at least 5.

## 2. Correct bridge placement and exact left-facing transformation

The earlier proposed placement of `4*(v₂(n)-1)` state-1 cycles immediately after a `12*a+6` prefix was not uniform in `a`. The corrected placement is **after** the existing `counted_left_sweep (3*a+1)`, which costs `9*a+3` and leaves state 3 at `hN=h-(3*a+1)`.

A fixed six-step prelude reaches state 1 at `hN`, blank under the head, with `3*v+4` ones to the left. The exact bridge then has:

1. a state-1 left sweep of `3*(v+1)` three-step cycles, cost `9*(v+1)`;
2. a fixed four-step exit to state 4 at `H=hN-3*(v+1)-2`;
3. a fixed three-step setup to state 5 at `H+3`;
4. a state-5 right sweep of `v+1` three-step cycles, consuming the `3*(v+1)` ones written by the left sweep;
5. a one-step state-5 exit to state 4 at `hN+2`, followed by the final three-cell q4 scan.

The bridge cost is `12*v+29`. The fixed prelude and source-boundary hypotheses are proved from the S1 encoding and the original transition table in the new source file.

The central bridge left-facing transformation is:

~~~lean
(∀ i, P (hN-i) = sideBit
  ([false,true,true,true,true] ++ d1pow v ++ d0 ++ tail) i) ->
(∀ i, bridgeTape v P hN (hN-i) = sideBit
  ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail) i)
~~~

The proof has three regions: the state-5 right-sweep blocks give the repeating modulo-3 prefix; the fixed exit gives the two-cell boundary and the three `d1` bits; the far-left exterior is preserved. The outer `counted_left_sweep (3*a+1)` supplies the prefix `[true] ++ d1pow a`.

Consequently the exact q4 cut left-facing stream at the original source head `h` is:

~~~lean
Q = [true] ++ d1pow a ++ markerWord 0 ++ d0 ++
      binDec L (n-1) ++ lh
~~~

The new `m1EvenValuation_q4_leftFacing` proves this pointwise from the outer sweep and bridge output. The target-left identity is:

~~~lean
s1LeftFacing L (n-1) 0 (a+b+2) (2^b-1) =
  d0pow b ++ d1pow 2 ++ Q.drop 1
~~~

It follows from `binDec_pow2_sub_one` and `d1pow_add_right`. The source also proves the exact q4 right shape and blank far tail from the S1 right-facing word, then calls the existing `q4_suffix_run_to_s1Config`.

## 3. Exact q4 suffix and counted-drain composition

The q4 suffix theorem has total length `39+3*b`. Its first four steps are the unchanged q4 guard, moving from state 4/head `h` to state 4/head `h+4`; the remaining `35+3*b` steps are composed after the source prefix, which already ends at state 4/head `h+4` with the same tape. This split is explicit in `m1EvenValuation_reset_prefix_source` and avoids replaying the first four transitions.

The source prefix ends at state 4/head `h+4` after `12*a+12*v+32` steps. The reset-prefix cost identity is:

~~~lean
resetPrefixCost 1 ((2*q+1)*2^v) a b =
  (12*a+12*v+32) + (35+3*b)
~~~

Adding the existing `s1Config_reset_prefix_then_counted_drain` gives the full `proposedIncrementCost 1 n a b` source theorem above. The endpoint is exactly `s1Config L (n-1) 0 (a+b+2) 0 (2^b-1) (h+5+3*b)`.

## 4. Sweep-coordinate sanity check

The two left-sweep block lemmas have different contracts and must not be interchanged:

- Outer sweep: `sweptLeft_block N j T h (hj : j+1<N)` writes true at `h-j`. The q4 cut proof uses `j=i` in the strict interior `i+1<N0`; the last index `i+1=N0` is handled separately by the bridge exit. The head cell uses `j=0` when `a>0`.
- State-1 bridge sweep: `state1SweptLeft_block N T h i (hi : i<N)` writes true at `h-N+1+i`. It proves the `rightOnes` block consumed by the later state-5 right sweep; it is not the outer q4 left-facing prefix lemma.

The current `M1EvenValuationSource.lean` uses each lemma with its correct coordinate and bound. In particular, the outer q4 proof's direct `sweptLeft_block N0 i` call is guarded by `i+1<N0`, while the bridge proof uses `state1SweptLeft_block N ... i` under `i<N`. The `sweptLeft_plus1 (3*a)` call supplies the cell at `h+1` for a sweep of length `N0=3*a+1`.

## 5. Consequence for the 24-cycle root itinerary

Let `R=tm63RootResidueSixK`, odd. The marker-1 indices after the relevant middle rows are `n_j=16*R-16-24*j`. Their valuation pattern is:

- odd `j`: `v₂(n_j)=3`;
- `j=2*u` with odd `u`: `v₂(n_j)=4`;
- `j=2*u` with even `u`: `v₂(n_j)>=5`.

This parity analysis remains useful motivation, but the new all-index source theorem covers all three cases (and more). The former separate valuation-four and valuation-at-least-five source obligations are no longer needed for marker 1. The remaining 24-cycle source gaps are the two residue-zero all-q families for markers 0 and 2, tracked in `TM63-24Cycle-Source-Coverage-20261117.md`.

## 6. Validation boundary

The committed `M1EvenValuationBridgeProbe.mjs` exercises the exact transition table and S1 encoding. It passed 480 cases with `L=16`, exact valuations `v=1..8`, odd quotients `q∈{1,3,5,7,9}`, `a∈{0,1,2,5,10,20}`, and `b∈{0,2}`. Every case ended state 4 at `h+4` after exactly `12*a+12*v+32` steps, and the full q4 cut guard/right tail/left stream matched. This is reproducible finite simulation evidence, not a formal proof.

The Lean source theorem is written and manually reviewed, but no compile result or axiom profile is claimed yet. The remaining action is exact original-import compilation of `M1EvenValuationSource.lean` and its transitive closure, followed by inspection of the `#print axioms` output. Do not treat the theorem as source-certified until that succeeds.

## 7. Historical diagnostic: the rejected `12*a+6` placement

The original placement of `4*(v₂(n)-1)` state-1 cycles immediately after a `12*a+6` prefix was disproved as a uniform source-tape argument. For `L=16,n=32,m=1,b=0`, the exact transition table gave:

| `a` | state after `12*a+6` | head | blank under head? | consecutive ones to left | required |
|---:|---:|---:|:---:|---:|---:|
| 1 | 1 | -4 | yes | 19 | 17 |
| 3 | 1 | -12 | yes | 17 | 17 |
| 5 | 1 | -20 | yes | 15 | 17 |
| 10 | 1 | -40 | yes | 10 | 17 |
| 20 | 2 | -82 | yes | — | 17 |

Thus the old fixed-sweep placement fails for authentic large `a`; the local state-1 sweep itself is valid. The corrected post-counted-sweep placement in sections 2–3 is the one now formalized in the source theorem.

## 8. Updated conclusion: all positive M1 indices are covered in the written source

The generic source theorem is not restricted to `v>=4`, to even `n`, or to a particular odd-quotient parity. It is stated for every `0<n<2^L` and `a>0`, and its factorization proof permits `v=0`. Therefore it covers the root's complete marker-1 subsequence without a separate valuation split. The only remaining status qualification is validation: the theorem is written and manually reviewed, but its Lean compilation and axiom audit are pending.

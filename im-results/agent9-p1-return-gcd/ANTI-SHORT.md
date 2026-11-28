# Coprimality-free negacyclic obstruction: a quotient-collision mechanism

**Status (28 November 2026):** pending opt-in original-source Lean audit (`anti-short`). This is intermediate structural work and does not decide P1 or BB(6). The proof route depends on the primitive-period cyclic theorem in [CYCLIC-SHORT.md](CYCLIC-SHORT.md).

## Main intended statement

Let `h>0` be odd, `K>0`, `h|(2^K+1)`, and suppose an interior doubling carry `0<a_j<h` with bits `x_j∈{0,1}` is accompanied by **both** positive affine-clock micro-coordinates `c_j,w_j∈[1,C]` for `K+B` steps. If

`h*(C+K+1)<2^B,`

then this trajectory is impossible, even when `gcd(h,K)>1`.

Previously the anti-shift proof in [AntiGeneric.lean](AntiGeneric.lean) deduced `h|K*(a_B-h)` from a halving determinant and used `gcd(h,K)=1` to infer a boundary contradiction. The new argument replaces that coprimality step:

1. `h|K*a_B` follows by adding the evident multiple `K*h`. The recurrence `2a_(j+1)=a_j+h*x_j` implies `K*a_j=2*(K*a_(j+1))-h*K*x_j`. Therefore divisibility propagates backward from time `B` to time zero, giving `h|K*a_0`, with **no modular inverse or parity cancellation**.
2. Negacyclicity from `h|(2^K+1)` gives `a_K=h-a_0`. Hence `h|K*a_K`. Applying the same backward propagation over the first `K` slope steps gives `h|K*a_j` for all `0≤j≤K`.
3. Write `K*a_j=h*b_j`. Since `0<a_j<h`, each `b_j` for `0≤j<K` is an integer with `0<b_j<K`. There are only `K-1` integer slots, so `b_i=b_j` for some `i<j<K`. The positive multiplier `K` forces `a_i=a_j`.
4. Uniqueness of interior predecessors transfers this collision to a genuine positive return `a_(j-i)=a_0` of length `p=j-i<K`. The cyclic [no_short_return_carry](CyclicShort.lean) theorem now excludes a bounded positive affine-clock path of length `K+B` as soon as a return `p≤K` exists.

This argument is robust to large common factors. For instance, `gcd(27,9)=9`, and the old approach could not divide out the factor 9 to reach a boundary. The quotient collision does not need to divide K or h.

## Original P1 trace corollary

For even `n≥14` and a genuine delayed-carry `Trace n m W a`, if `h` is odd, `K>0`, `h|(2^K+1)`, and

`h*(7*2^n+K+1)<2^B,`

then equal or bitwise-complemented length-`n+3+K+B` factors cannot occur at shift `h*2^r`. The first `n+3` selected steps settle the normalized slope; the last `K+B` steps invoke the quotient collision. This covers disjoint as well as overlapping factors.

For every even `n≥14` the explicit candidate Lean corollaries are:

| Shift | Divisibility witness | Coprimality failure | Excluded length |
|---|---|---|---|
| `9*2^r` | `9|2^3+1` | `gcd(9,3)=3` | `2n+12` (`B=n+6`) |
| `27*2^r` | `27|2^9+1` | `gcd(27,9)=9` | `2n+20` (`B=n+8`) |
| `81*2^r` | `81|2^27+1` | `gcd(81,27)=27` | `2n+40` (`B=n+10`) |

These examples illustrate a whole number-theoretic direction based on powers of three; no unproved infinite-family Lean theorem is asserted here.

Source files: [AntiShortCore.lean](AntiShortCore.lean) (backward divisibility and quotient collision), [AntiShort.lean](AntiShort.lean) (abstract negacyclic contradiction), [AntiShortScaled.lean](AntiShortScaled.lean) (dyadic and boundary regimes), [AntiShortTrace.lean](AntiShortTrace.lean) (original `Trace`), [AntiShortExamples.lean](AntiShortExamples.lean) (three explicit values).

**Next key task after checking Lean:** exploit the excluded factors in a true P1 endpoint search. No present argument forces a hypothetical long trace to contain any such factor, and thus this alone is not a nonhalting certificate.

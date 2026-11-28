# One-period cyclic-order obstruction for genuine P1 delayed-carry traces

**Status (28 November 2026):** Lean source and original-Trace bridges are being audited in the opt-in Agent9 P1 workflow; this file records the mathematical argument and precise scope. Do not treat the new source theorems or numerical examples as kernel-accepted until the workflow succeeds, with no errors or nonstandard axiom dependencies. This is an **intermediate structural restriction**, not a P1 halting decision or an upper bound for BB(6).

## New primitive-period arithmetic lemma

Let `g>0`, `p>0`, and integers `0<a_j<g` (`0<=j<=p`) satisfy `d a_(j+1)=a_j+g x_j` for some fixed integer multiplier `d`, with `a_p=a_0` and no repeated `a_j` among `j<p`. Then **`g` cannot divide `p*a_0`**. (The Lean file specializes to `d=2`.)

Proof by contradiction: divisibility `g|p*a_p` propagates *backward* since

`p*a_j = d*(p*a_(j+1)) - g*p*x_j`.

Thus `g|p*a_j` at every `j<p`. Writing `p*a_j=g*b_j` yields `0<b_j<p`. Equality of two `b_j` forces equality of two `a_j`, so the `p` values `b_0,...,b_(p-1)` are distinct positive integers below `p`: impossible. **No `gcd(g,p)=1` or upper bound `p<=B` is required.** Unlike the alternative proof using a 2-adic inverse, backward propagation does not require cancelling the multiplier `d` modulo `g`.

Formalization: [CyclicPrimitive.lean](CyclicPrimitive.lean), theorem `primitive_product_not_dvd`.

## One-period affine-clock rigidity

Suppose `g>0` is odd, the integral slope and clock follow

`2 a_(j+1)=a_j+g x_j,`  `2 c_(j+1)=c_j+(q+dir*j)x_j,`

with `dir in {+1,-1}`, `x_j in {0,1}`, `0<a_j<g`, `1<=c_j<=C`. If `a_k=a_0` for some `0<k<=K`, extract the least positive return `p<=K`. Oddness of `g` makes the bits `x_j` repeat with period `p` wherever both copies are in the finite interval.

For `b_j=dir*(c_(j+p)-c_j)` and `E_j=g*b_j-p*a_j`, direct cancellation of the clock slopes gives

`2 b_(j+1)=b_j+p*x_j`,  `2 E_(j+1)=E_j`.

If the history has `K+B` steps and `g*(C+K+1)<2^B`, then `|E_0|<2^B`; integrality and `B` halvings force `E_0=0`. Consequently `g|p*a_0`, contradicting the primitive-period lemma. Thus a return costs at least **`K+B+1`** integral steps under the stated bound. Earlier `no_bounded_return_slope` needed `2K+B` to null the *second* difference; the primitive arithmetic lemma removes that extra period, even when `gcd(g,K)>1`.

Formalization: [CyclicShort.lean](CyclicShort.lean), `no_short_return_carry`, `no_short_mersenne`, and the scaled theorem `no_scaled_short`. [CyclicOrder.lean](CyclicOrder.lean) independently derives the coprime case through `gcd(g,K)=1`, without the primitive quotient argument.

## Transfer to an original delayed-carry Trace

For an authentic `BB6.Agent45.DelayedCarry.Trace n m W a` with even `n>=14`, the source-linked `trace_path` provides genuine positive micro-coordinates `v_j,w_j<=T=7*2^n`, with their clock slope `T-n-j-3` and selected bits `x_j=bit W j`. If two factors distance `s=2^r*h`, `h` odd, agree up to complement, their coordinate difference obeys the slope recurrence with `g=s`. After `n+3-r` settling steps, its odd slope `h` is confined to `[0,h]`. Boundary values force a positive coordinate to halve `B` times, impossible when `T<2^B`. An interior slope has a return within any positive `K` with `h | (2^K-1)`, by the existing `order_return` lemma.

Therefore, for any `K>0`, odd `h`, `h|(2^K-1)`, and integer `B` such that

`h*(7*2^n+K+1)<2^B,`

a true Trace cannot have equal **or bitwise-complemented** factors at shift `2^r*h` with length `n+3+K+B`. This includes overlapping and disjoint factors, and does **not** assume `gcd(h,K)=1` or `K<=B`.

Formalization: [CyclicTraceShort.lean](CyclicTraceShort.lean), `trace_no_odd_short_repeat`, built on unchanged [ReturnTrace.lean](ReturnTrace.lean), [ReturnScaled.lean](ReturnScaled.lean), and [LagCore.lean](../agent45-p1-delayed-carry/LagCore.lean). Neither selected-factor statement decides whether a critical endpoint is reached.

Examples for every even `n>=14`:

| Shift | Order witness | `B` | Forbidden factor length | Earlier `2K` bound |
|---|---:|---:|---:|---:|
| `9*2^r` | `9|2^6-1` | `n+7` | `2n+16` | `2n+19` |
| `27*2^r` | `27|2^18-1` | `n+8` | `2n+29` | `2n+43` |
| `47*2^r` | `47|2^23-1` | `n+9` | `2n+35` | `2n+53` |

The 9 and 27 examples have nontrivial `gcd(h,K)`; the older coprime determinant alone cannot handle them. The extra `B` bound is checked arithmetically for each n. Source specialization: [CyclicExamples.lean](CyclicExamples.lean).

## Limits and next tests

- Required: original-source Lean 4.36.0-rc2 compilation with `#print axioms` excluding `sorryAx`; the workflow targets `cyclic-order` in `.github/workflows/agent9-p1-shadow-depth.yml`.
- Potential direct use: add forbidden equal/complement windows at selected `2^r*h` shifts to P1 symbolic trace or exact prefix search when windows become long enough.
- Unsolved: prove that every hypothetical true P1 critical trace necessarily contains such a forbidden factor. This theorem alone cannot exclude any new `n`, let alone determine BB(6).

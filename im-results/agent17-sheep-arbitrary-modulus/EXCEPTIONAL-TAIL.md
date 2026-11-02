# Uniform elimination of exceptional Sheep predecessors for arbitrary symbolic families

**Status:** intermediate mathematical result, with a complete elementary written proof and deterministic exact-integer tests. The generic-branch modular gap is separately kernel-checked in `GeneralOddGap.lean`. The exceptional-branch theorem below is **not yet Lean-kernel formalized**. It gives a reusable finite-exception cutoff for symbolic inverse trees, and does not decide the actual Sheep blank orbit or BB(6).

The published Sheep return map has a special nonhalting branch
`F(3*2^a)=3*2^a+a+3` for every natural valuation `a`. Let `c>=1`, `s>=0`, `d>=1`, `b∈ℤ`; note that unlike generic-parent congruences, **d need not be odd here**. Consider the symbolic target

`Y(j)=(c*2^(j+s)+b)/d`.

An exceptional source would necessarily satisfy, on multiplying by d,

`C*2^j+b = D*2^a+d*(a+3)`, where `C=c*2^s>0` and `D=3*d>0`. (E)

## Effective all-exponent theorem

First choose any integer `B>=1` for which

1. `D*2^B > C+|b|`,
2. `C*2^B > D`.

Such B exists by exponential growth. Next choose any integer `J` with

3. `J>=2*B+|b|+4`,
4. `2^(J-B) > d*(J+B+3)+|b|`.

Such J likewise exists. **Then for every natural j>=J and every natural a, equation (E) is impossible.**

### Proof: exhaustive position of the exponent a

The strict inequality (4) persists when j increases beyond J, since its left side doubles while the right side increases by only d and the left side already exceeds d. Thus for every j>=J,

`2^(j-B)>d*(j+B+3)+|b|`. (5)

**High valuation: `a>=j+B`.** Using condition 1,

`D*2^a >= D*2^(j+B) > (C+|b|)*2^j >= C*2^j+b`.

The right side of (E) is strictly greater still after adding `d*(a+3)`. Impossible.

**Low valuation: `a<=j-B`.** Condition 2 gives the positive integer `C*2^B-D>=1`; hence, using (5),

`C*2^j+b-D*2^a >= (C*2^B-D)*2^(j-B)-|b| >= 2^(j-B)-|b| > d*(j+B+3) >= d*(a+3)`.

Impossible.

**Middle valuation: `j-B<a<j+B`.** Write `V=C*2^j-D*2^a`. Both terms are divisible by `2^min(j,a)`, and `min(j,a)>=j-B+1`. If V is nonzero, its absolute value is at least `2^(j-B)`, whereas equation (E) would require

`|V|=|d*(a+3)-b| <= d*(j+B+3)+|b| <2^(j-B)`,

contradiction. If V=0, (E) forces `b=d*(a+3)`. But condition 3 and `a>j-B` give `a>=j-B+1>=B+|b|+5`, so `d*(a+3)>|b|>=b`, another contradiction.

The three cases exhaust the nonnegative integer a. QED. This proof does not invoke any unverified modular period, bound the actual blank trajectory, or assume anything about the fraction's integrality.

## Reproducible cutoff construction

`exceptional_uniform.py` computes B by doubling until conditions 1–2 hold, then sets `J=2*B+|b|+4` and increases J until condition 4 holds. It uses exact Python integers, has no third-party dependencies, and always terminates. The local Python 3.11 run tested **4,000** signed symbolic families and **651,923** exact exceptional-branch inequalities at each family's guaranteed horizon and higher exponents:

```
PASS: 4000 signed coefficient families; 651923 exact exceptional-branch inequalities
(1, 0, 0, 1) (2, 8)
(3, 0, 0, 1) (1, 6)
(3, 0, -500, 1) (8, 520)
(1, 7, 21, 3) (5, 35)
```

The first element of each displayed tuple is `(c,s,b,d)` and the result `(B,J)`. These bounds are deliberately conservative. A separate exact source result by Agent 14 already classifies immediate predecessors of the special `3*2^j` family more sharply.

## Consequence for the symbolic inverse-family algorithm

Combine this theorem with `GeneralOddGap.lean` and `GENERAL-TAIL.md`:

- For a fixed family `(c,s,b,d)` with d positive odd, there is an explicit **finite upper bound A** for any generic parent valuation `a` independent of j.
- There is also an explicit **exceptional cutoff J** such that no special odd-part-three parent of any member `Y(j)`, `j>=J`, can exist.
- The remaining finite generic parent valuations can be handled by exact modular periods (see `PeriodCore.lean`), keeping the inverse algorithm mathematically sound for arbitrary positive c.

These statements ensure local inverse branching becomes effectively finite above J. They do **not** imply that the entire inverse tree closes. Agent 22/39 already constructed real valuation-zero inverse paths of unbounded length into powers of two. A decisive proof must additionally restrict forward reachability from the genuine starting state t=5 or prove a genuinely unbounded-depth invariant.

**Prior credit:** Agent 17's earlier c=1 inverse sieve already had a more economical specialized exceptional-bound method; Agent 14's published-in-repo c=3 special case predates this general algorithm. The new contribution is uniformity in arbitrary coefficients and offsets, not those existing special results.

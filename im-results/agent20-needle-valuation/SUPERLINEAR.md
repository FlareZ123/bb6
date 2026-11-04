# Space Needle terminal predecessor exponents grow superlinearly in their 2-adic valuation

**Agent 20, 2026-11-04. A new elementary, all-parameter mathematical theorem. Status: complete hand proof with explicit constants and independent finite arithmetic cross-check; general theorem is *not yet Lean formalized* and is not a blank-root classification.** The original high-level predecessor identity is established in unchanged source by Agent48. This note is in `im-results/` because neither external mathematical novelty nor a new BB(6) bound is established.

## Theorem: every fixed exponent slope is eventually forbidden

Let `c,q,v,K` be natural numbers, with `c>=1`, and suppose

```text
  2^K = 2^v*(2q+3) + v + 3*(q+1).            (1)
```

Then the following **explicit, uniform implication** holds:

```text
  v >= 4*(3^c+1)    implies    K > c*v.       (2)
```

Thus, along *any* sequence of legal immediate predecessors of powers of two whose valuations `v` go to infinity, the quotient `K/v` tends to `+infinity`. In conventional asymptotic notation, `K=Omega(v log v)` for legal predecessors with `v` sufficiently large: choose `c=floor(log_3(v/4-1))` (for `v>=16`). This is a theorem about **all unrestricted high-level incoming edges**, without assumptions about the blank-start orbit.

The earlier locally kernel-checked [sharp bound](README.md) supplies `K>=2v+1` for every individual edge; the new statement says that *every* fixed linear slope fails for sufficiently large valuations.

## Proof

Assume `v>=4*(3^c+1)` and toward a contradiction `K<=c*v`. Put

```text
A=3^c,   M=A+1,    D=2^(v+1)+3.
```

In particular `v>=16`, `2v-3>0`, and the elementary induction `2^v>=v^2` for `v>=4` applies. Rearranging equation (1) yields the exact identity

```text
2^(K+1) = D*(2q+3) + (2v-3).                  (3)
```

By Euclidean division write

```text
K+1 = t*(v+1)+r,    0<=r<=v.
```

Since `K<=c*v` and `c>=1`, we have `0<=t<=c`. In integers modulo `D`, equation `2^(v+1)=-3 (mod D)` gives from (3)

```text
(-3)^t * 2^r = (2v-3) + m*D                    (4)
```

for some **signed integer** `m`.

First bound the quotient. Since `3^t<=A`, `r<=v` and `2v-3<=2^v`,

```text
|m|*D <= A*2^r+(2v-3) <= (A+1)*2^v=M*2^v.
```

As `D>2*2^v`, in particular `|m|<=M`.

Rearrange (4) as

```text
2^r * [(-3)^t - m*2^(v+1-r)] = 2v-3+3m.    (5)
```

The bracket is an **odd, nonzero integer** because `(-3)^t` is odd and `v+1-r>=1` makes its other term even. Consequently

```text
2^r <= |2v-3+3m| <= 2v+3M.                   (6)
```

Substitute (6) back into the magnitude of (4):

```text
|m|*D <= A*2^r+(2v-3)
       <= (A+1)*(2v+3M)
        = M*(2v+3M).
```

But `v>=4M` gives

```text
M*(2v+3M) <= 3*M*v <= 3*v^2/4
                         < v^2 <= 2^v < D.
```

Therefore `|m|<1` and `m=0`. Equation (4) now states

```text
(-3)^t*2^r = 2v-3 > 0, an odd integer.
```

Its positivity forces `t` even, and its oddness forces `r=0`.
Thus `2v-3=3^t<=3^c=A`, whereas
`v>=4(A+1)` implies `2v-3>=8(A+1)-3>A`.
Contradiction. Hence `K>c*v`, proving (2).

Every division, modulus and absolute-value step above is exact. This is a stand-alone elementary proof of the all-natural implication. It invokes no probabilistic model, asymptotic estimate inside the argument, or computer enumeration.

## Reproducibility and evidence levels

The source identity (1), including the fixed parameters `q,v`, is transported from the pinned original Space Needle acceleration by Agent48's source-checked `SpaceNeedleClosed.lean`; see [their dossier](../agent48-space-needle/README.md).

- The simpler sharp threshold `K>=2v+1` and its unique equality case are **locally Lean-kernel checked**, see `A20NeedleGap.lean` and `A20UniqueBoundary.lean`.
- The *new superlinear theorem* (2) has the detailed complete human proof above. **No Lean kernel certificate yet** for its quantification over arbitrary `c`. Treat it as a human mathematical proof, not a verified Lean theorem.
- Independent exact-big-integer modular enumeration checked **965,856** candidate `(v,K)` pairs with `16<=v<=1000`, `2v+1<=K<=cv`, and maximal `1<=c<=6` meeting the threshold `v>=4*(3^c+1)`. It found **zero counterexamples**. The checker only tests necessity from equation (1), not a blank orbit. It is auxiliary to the proof.
- Explicit threshold examples: `c=1: v>=16`, `c=2: v>=40`, `c=3: v>=112`, `c=4: v>=328`, `c=5: v>=976`, `c=6: v>=2920`.

## Novelty, interpretation and next action

This gives a genuinely stronger unrestricted **one-step terminal-predecessor valuation ceiling** than the simple linear bound, using the oddity of `(-3)^t-m2^(v+1-r)` and the fact that a bounded exponent ratio bounds `t`. Its possible relevance is to reduce the valuations in exact predecessor enumeration from `O(K)` to `O(K/log K)`, asymptotically. No root reachability condition has been incorporated. It cannot prove the true blank-start orbit avoids incoming edges and therefore cannot decide Space Needle or BB(6).

Closest public source: Katelyn Doucette, *All About Space Needle* (2025), <https://katelyndoucette.com/articles/all-about-space-needle>, which already derives the one-step congruence for a fixed valuation. The original publication treats multi-step backward search, and this note claims no external priority. The next valuable steps are independent mathematical review, optional Lean formalization, and testing whether the one-step bound can be combined with a genuine blank-orbit invariant or a multi-step inverse-word restriction.

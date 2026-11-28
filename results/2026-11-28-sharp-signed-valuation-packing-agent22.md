# Sharp universal finite packing bound for four-adic signed inverse edges

**28 November 2026 — Agent 22. Exact extremal formula and mathematical proof, with a finite, machine-reproducible base certificate.** This result sharpens the existing source-independent signed inverse edge budget in [`ValuationEdges.lean`](../im-results/agent22-429-signed-drift/ValuationEdges.lean). The original `edge_family_budget` proved `6·∑j < K`; the theorem below improves the constant to **15/2**, and this new constant is optimal for general admissible edges. This paper argument has **not yet been checked end-to-end by Lean**. It does not decide #429 or BB(6), nor does it establish a universal Busy Beaver upper bound.

## Theorem: sharp signed-edge valuation budget

Fix an integer **K≥15**, and finitely many triples of positive integers
[
(v_i,j_i,w_i),qquad i=1,ldots,N,
]
such that
[
0<v_i,quad 3v_i<K,quad j_ige1,quad
4^{j_i}w_i=v_i+K.
]
Suppose the source integers `v_i` are pairwise distinct. Then
[
oxed{quad 15sum_{i=1}^N j_i le 2K.quad}
]
The coefficient **15/2 is sharp**: the single edge `K=15, v=1, j=2, w=1` satisfies every hypothesis and has `15j=30=2K`.

For `1≤K<15`, the intermediate uniform interval estimate below can exceed `2K/15` only at `K=7,13,14`; consequently the theorem deliberately uses the exact hypothesis `K≥15`. In particular, it would be false to advertise the 15/2 statement as a theorem for all positive K.

## Stronger exact extremal theorem: the capacity is attained at every K

The sharp **per-K** result is stronger than the uniform 15/2 inequality. For *every positive integer K*, consider all finite edge families as in the theorem above, requiring distinct positive source values (the inequality `K≥15` is not needed). The **exact maximum** of their total exponent weight is
[
oxed{displaystyle
J_{max}(K)=
Fleft(leftlfloorrac{K-1}{3}ightflooright)
-
Fleft(leftlfloorrac K4ightflooright)
=U(K).}
]
The upper bound is proven in the next section. **Every summand can be attained simultaneously:** for each integer `z` satisfying `K/4<z<K/3`, let `e=ν_4(z)`, and explicitly choose
[
v=4z-K,qquad j=e+1,qquad w=z/4^e.
]
All three entries are positive integers; `3v<K` is equivalent to `z<K/3`, and `4^j w=4z=v+K`. **Even the target** satisfies the same strict cone `0<3w<K`, since `0<w=z/4^e≤z<K/3`. Distinct `z` give distinct `v`. Summing `j=1+ν_4(z)` over *all* the interval integers yields exactly `U(K)`. This exhibits a maximizing family and proves the capacity formula **without an asymptotic or compactness argument**.

These maximizing edges are an abstract extremal family, not necessarily successive edges of one cyclic inverse path. Thus the exactness of `U(K)` for unconstrained **edge families** does not imply that a signed path with that total valuation weight exists.

### Asymptotically exact capacity constant: 9

Write `s_4(n)` for the sum of base-4 digits of `n`. A routine division-by-4 summation gives the exact digit identity
[
F(n)=rac{4n-s_4(n)}3.
]
Indeed, `n=4q+r` gives `F(n)=n+F(q)` and `s_4(n)=r+s_4(q)`; induction on `n` proves the identity. Consequently, with the same `a,b` as above,
[
U(K)=rac43(b-a)+rac{s_4(a)-s_4(b)}3
=rac K9+O(log K).
]
Here `b-a=K/12+O(1)`, while each digit sum has at most `1+lfloorlog_4 Kfloor` digits, each at most three. Therefore
[
oxed{lim_{K	oinfty}rac{J_{max}(K)}{K}=rac19.}
]
The asymptotic coefficient **9** for the ratio `K/J` is itself optimal for large-K *unconstrained edge families*, because the constructive family above attains `J_{max}(K)` for every K. The globally valid constant 15/2 is smaller only because small K (specifically K=15) has a locally denser four-adic interval.

## Proof by exact valuation summation

Define
[
z_i:=4^{j_i-1}w_i.
]
Because `j_i≥1`, the defining edge equation becomes `4z_i=v_i+K`. Using `0<v_i` and `3v_i<K` gives the **strict open interval**
[
rac K4<z_i<rac K3.
]
Distinct sources imply distinct `z_i` (since `v_i=4z_i-K`). Since `4^{j_i-1}` divides `z_i`, writing `ν_4(z)` for the largest `e≥0` such that `4^e|z` yields
[
j_ile 1+
u_4(z_i).
]

Define the finite *valuation capacity* of this open interval:
[
U(K)=sum_{substack{zinmathbb Z_{>0}\K/4<z<K/3}}!!(1+
u_4(z)).
]
All `z_i` are distinct, so immediately
[
sum_i j_ile U(K).
]

Let `F(n)=sum_{a=0}^{infty}lfloor n/4^afloor`, a finite sum for integer `n≥0`. By counting, for each positive integer `z≤n`, the levels `a≥0` with `4^a|z` are exactly `1+ν_4(z)`, hence `F(n)=sum_{1≤z≤n}(1+ν_4(z))`. With
[
b=leftlfloorrac{K-1}{3}ightfloor,qquad
a=leftlfloorrac K4ightfloor,
]
the strict interval has exactly the integers `a<z≤b`, giving the **exact arithmetic identity**
[
oxed{U(K)=F(b)-F(a).}
]

### Infinite-range inequality (K≥151)

The geometric-series bound `F(n)≤(4/3)n` holds because `floor(n/4^i)≤n/4^i`. Also `F(a)≥a+floor(a/4)+floor(a/16)`. The identities `floor(floor(K/4)/4)=floor(K/16)` and `floor(floor(K/4)/16)=floor(K/64)` then imply
[
egin{aligned}
U(K)
&le 	frac43leftlfloorrac{K-1}3ightfloor
 -left(leftlfloorrac K4ightfloor+
 leftlfloorrac K{16}ightfloor+
 leftlfloorrac K{64}ightflooright)\
&lerac{4(K-1)}9-rac K4-rac K{16}-rac K{64}+3\
&=rac{67}{576}K+rac{23}{9}.
end{aligned}
]
Since
[
rac{2}{15}-rac{67}{576}=rac{49}{2880},
]
we have
[
rac{67}{576}K+rac{23}9lerac{2}{15}K
quadLongleftrightarrowquad
49Kge7360.
]
Every integer `K≥151` satisfies this last inequality, proving `15U(K)≤2K` in the infinite range.

### Finite exact base range (15≤K≤150)

The remaining **136** integers are checked with integer arithmetic using the exact formula `U(K)=F(floor((K-1)/3))-F(floor(K/4))`. The stand-alone, deterministic, no-dependency finite certificate is [`sharp_packing_small.cjs`](../im-results/agent22-429-signed-drift/sharp_packing_small.cjs). Its complete essential loop is:

```js
function F(n) {
  let s=0;
  while(n>0) { s+=n; n=Math.floor(n/4); }
  return s;
}
function U(K) {
  return F(Math.floor((K-1)/3))-F(Math.floor(K/4));
}
for (let K=15;K<=150;K++) {
  if (15*U(K)>2*K) throw new Error("counterexample "+K);
}
```

The evaluation reports zero counterexamples and one equality, at `K=15`. A separate audit of `1≤K≤14` reports that the *capacity* `15U(K)>2K` only for `K=7,13,14`, documenting the theorem's range restriction. All arguments use exact safe-range integers; the full proof has no probabilistic, asymptotic, or floating-point step. Combined with the infinite-range inequality, the bound holds for **every K≥15**, completing the proof. `□`

## Why the new constant matters mathematically

The previous admissible quotient packing sent `j` different levels per edge into the union of intervals `(0,K/12)∪(K/4,K/3)`, counting at most `(K−1)/6` integer slots. The new argument instead uses **only one quotient in the upper interval per edge but charges its exact four-adic multiplicity**. This captures the restrictive fact that a large `j` must arise from unusually highly 4-divisible upper quotients, a phenomenon lost by counting slots equally.

For a finite cycle of the signed inverse slope recurrence
[
4^{j_i}v_{i+1}=v_i+K,qquad 0<3v_i<K,
]
with primitive period and therefore pairwise distinct source values, the theorem gives
[
Kgerac{15}{2}sum j_i
]
provided `K≥15`. The old necessary inequality was only `K>6sum j_i`. This is a strict improvement to the primitive-cycle obstruction. The new sharp bound does **not** imply that an infinite admissible mixed-path orbit cannot exist; it addresses a finite distinct-source family and source-independent arithmetic, not the missing authentic blank-to-terminal ancestor quantifier.

### Corollary: an integer-slope obstruction without the parity hypothesis

Let `W` be a nonempty typed E/S pair-word whose **positive gap sequence** `(j_1,...,j_a)` has primitive period equal to its whole word length, and suppose at least one `j_i>1`. Put `J=∑j_i` and `T=∑(3j_i+2)` for E letters or `∑(3j_i+4)` for S letters. Then there is **no** nonzero cyclic integer sequence `s_1,...,s_a` satisfying
[
0<3s_i<T,qquad 4^{j_i}s_{i+1}=s_i+T
]
(indices modulo `a`). This applies to arbitrary E/S type allocations and does **not** assume the slopes `s_i` are even.

**Proof.** By the exact predecessor-uniqueness argument already formalized in [`ValuationPrimitive.lean`](../im-results/agent22-429-signed-drift/ValuationPrimitive.lean), equal slope sources at two phases of a cyclic path force equality of every preceding exponent; a primitive exponent period therefore makes the `s_i` pairwise distinct. Applying the sharp packing theorem with `K=T`, for `T≥15` we obtain
[
15Jle2Tle14J,
]
impossible since `J>0`. The last inequality follows termwise from `3j+4≤7j` for each `j≥1`.

If `T<15`, the condition that some `j>1` leaves **exactly seven** possible typed words, irrespective of primitive-period status (their order matters):
`E2` (`T=8,J=2`), `S2` (`10,2`), `E3` (`11,3`), `S3` (`13,3`), `E4` (`14,4`), `E1,E2` (`13,3`), and `E2,E1` (`13,3`). Their exact valuation capacities `U(T)` are respectively `0,1,1,2,2,2,2`, all **strictly below J**. Since any distinct-edge cycle would imply `J≤U(T)`, none exists. Thus the conclusion holds for all possible `T`. `□`

**Connection to finite powers.** If enough consecutive copies of a typed word have an exact affine first-coordinate transfer, the finite second-difference argument in [`FinitePowerObstruction.md`](../im-results/agent22-429-signed-drift/FinitePowerObstruction.md) forces a positive integer slope `s` with `(M-1)s=A T`. The direct coefficient identity `M-1-3A=∑(4^{j_i}-4)·prefixScale` yields `3s<T` whenever some `j_i>1`. The slope difference transported through each letter satisfies `4^{j_i}s_{i+1}=s_i+T`, so the new corollary **excludes a sufficiently large finite power of any primitive-gap typed word without relying on parity at all**. This inference remains a paper-level combination; Lean acceptance of the finite source bridges is a separate obligation. Words whose typed period is *twice* their primitive gap period require the separate parity/half-rank argument from the prior [cyclic note](../im-results/agent22-429-signed-drift/FiniteTripleNoGo.md). There is no full inverse-path termination claim here.

### Reproducibility and formalization target

Run
```bash
node im-results/agent22-429-signed-drift/sharp_packing_small.cjs
```
to check the finite base with a built-in exact result assertion. For a Lean kernel proof, use the existing `ValuationEdges.Edge` structure, define `z` and a finite `ν_4` capacity sum, prove the injection `v_i↦z_i` and the `j_i` valuation charging inequality, then formalize the elementary `F` bound and close `15≤K≤150` by decidable computation. The underlying existing edge source assumptions have already been formalized; the **new sharp constant is proved here on paper and by a finite arithmetic check, not yet by the Lean kernel**.

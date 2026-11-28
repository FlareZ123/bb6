# A finite-power obstruction for #429 signed inverse pair words

**Status (28 November 2026): new paper-level arithmetic theorem and an exact-integer executable necessary-condition checker.** The argument uses the source-independent `PeriodicMacro.Walk` and exact E/S+even-F macro bridge already present in this directory. The universal arbitrary-repeat theorem and its composition with the original #429 source have **not** been compiled as a new Lean statement. It proves no blank-start verdict. The filename belongs under `im-results/`, not `results/`.

## Exact necessary condition, for any typed word

A letter is `E_j` or `S_j`, with `j>=1`, representing E/S followed by `2(j-1)` standalone F blocks. For a nonempty fixed finite typed word W, let its exact first-coordinate/half-rank transfer be

```text
    M*u_next = u + A*r + B,       r_next = r+T,
    M = product(4^j) = 4^J,
    T = sum(3*j+2 for E_j, 3*j+4 for S_j).
```

The integer coefficients M,A,B,T are precisely the recursive definitions in [PeriodicMacroTransfer.lean](PeriodicMacroTransfer.lean): for W=x::tail, `M=4^j*M_tail`, `A=1+4^j*A_tail`, `B=cost(x)+4^j*(A_tail*rankCost(x)+B_tail)`, `T=rankCost(x)+T_tail`. In particular M>=4, A,T>0.

**Theorem (finite-power affine forcing).** Suppose the *same complete typed word W* is traversed q consecutive times by an exact, nonnegative signed macro path, q>=3. Denote its paired inputs by (u_0,r_0),...,(u_q,r_q), where `r=(6u+D)/2`, `D>=0`, and each occurrence of the first letter has the same E/S guard. Define

```text
                 H = floor((r_0+2*T)/3).
```

If

```text
                 M^(q-2) > 2*H,                         (1)
```

then the first three pair-input first-coordinates are exactly affine:

```text
    u_0 + u_2 = 2*u_1,          (M-1)*(u_1-u_0) = A*T. (2)
```

Moreover `s=u_1-u_0` is a **positive even integer**, because `A*T>0` and the fixed E/S input guard forces u_0 and u_1 to have the same parity. Consequently

```text
                 2*(M-1) divides A*T.                  (3)
```

Failure of (3), together with (1), is a *complete mathematically exact exclusion of those q copies*, not a sampling heuristic. It does **not** require W to be primitive or have a positive F-run.

### Proof of the finite-power lemma

Transfer and rank additivity give, for n=0,...,q-1,

```text
  M*u_(n+1) = u_n + A*(r_0+n*T)+B,     r_n=r_0+n*T.
```

Write `delta_n=u_(n+2)-2*u_(n+1)+u_n` as a signed integer for n=0,...,q-2. Subtracting three consecutive transfer equations gives

```text
  M*delta_(n+1) = delta_n  (0<=n<=q-3),
  hence delta_0 = M^(q-2)*delta_(q-2).
```

Since `3*u_n <= r_n` at n=0,1,2, the first three nonnegative integers `u_n` are <=H. Thus `|delta_0|<=2H`. Under (1), the integer multiple `delta_0` of `M^(q-2)` must vanish. The difference of the n=1 and n=0 transfer equations then yields `(M-1)*(u_1-u_0)=A*T`. The E/S parity guard proves the slope even. This proof needs only q finite copies and their literal endpoint configurations, not eventual periodicity, an infinite path, or an unproved limiting argument.

The previously documented triple-word lemma is q=3. **The new leverage is the exponent q-2:** for four copies the required denominator is M squared; for five it is M cubed. The bound H uses only the *first three* boundaries and does not inflate with q.

## An additional two-copy square obstruction (stronger at short repetitions)

There is also a genuinely **two-copy** necessary condition, independent of the higher-power threshold (1). Suppose W is traversed twice, giving three paired boundaries (u0,r0), (u1,r0+T), (u2,r0+2T). From the two exact transfers,

```text
    A*T = M*(u2-u1) + (u0-u1).                          (7)
```

Set `H0=floor(r0/3)`, `H1=floor((r0+T)/3)`. Since `D>=0` at the first two boundaries, `0<=u0<=H0`, `0<=u1<=H1`; hence

```text
    -H1 <= A*T - M*k <= H0,    k=u2-u1 integral.       (8)
```

Writing `rho = A*T mod M` as a least nonnegative residue, **two complete copies are impossible if**

```text
    rho > H0   AND   M-rho > H1.                       (9)
```

Proof: no integer in the interval [-H1,H0] can have residue rho modulo M under (9). This is a one-sided *asymmetric modular-gap certificate*; the inequalities need no hypothetical third copy or primitive word, and do not require computing an entire path. It is sound for all finite, original signed E/S+even-F macro walks satisfying the source's guards.

If **three** W copies exist, u2 must also satisfy the same first-letter type guard as u0 and u1. Their parity agrees; therefore k=u2-u1 is even, strengthening (8)-(9) by replacing modulus M with **2M**. This is separate from the second-difference power obstruction and can reject three copies even when M is below the threshold (1). Importantly the modulus for **two copies alone is M, not 2M**: u2 is merely an output, with no guarantee that a hypothetical third W's entry guard holds. The exact BigInt pruner below implements both variants.

For q>=3 the combined pruner rejects if either the two-copy modulo-M gap, the three-copy modulo-2M gap, or the large-power even-slope divisibility condition fails. If q=2 it uses only the first. These are exact *necessary* conditions, not an exhaustive decision for the signed inverse model.

## Exact rank-delay corollaries (finite-word power growth)

The same integer inequalities admit a useful **inverted formulation**: how large must the half-rank already be *before* a repeated word is even arithmetically eligible?

Let `rho_m = (A*T) mod m` in the least nonnegative convention. Inverting the two-copy bounds (9), a legal square W² requires

```text
  r0 >= max(0, min(3*rho_M, 3*(M-rho_M)-T)).          (10)
```

For three or more copies the known same-type guard at u2 upgrades this necessary bound to

```text
  r0 >= max(0, min(3*rho_(2M), 3*(2M-rho_(2M))-T)).   (11)
```

These follow *exactly*, without approximation: e.g. `rho_M<=floor(r0/3)` iff `r0>=3*rho_M`, and `M-rho_M<=floor((r0+T)/3)` iff `r0>=3*(M-rho_M)-T`. A fixed word with non-resonant `rho_M` therefore cannot appear as a square until rank proportional to `M=4^J`, exponential in its total F-run exponent J.

For **q>=3** and `2*(M-1)` not dividing `A*T`, a legal q-th power additionally requires

```text
  r0 >= max(0, (3/2)*M^(q-2)-2*T).                   (12)
```

Here the quotient `M^(q-2)/2` is integral because `M=4^J` and J>=1. Indeed if the right-side bound failed, then `M^(q-2)>2*floor((r0+2T)/3)`, forcing the impossible even slope by the theorem. This is an **exact exponential delay for every fixed non-even-slope typed word**, not a probabilistic large-scale extrapolation. It also provides a computable upper bound on the repetition exponent at any fixed starting half-rank.

**Weighted onset bound along an entire signed path.** Let an initial signed pair half-rank be `r_init`. Let `I` be the sum of the positive exponents j in all typed letters *before* a repeated W, and let `J=sum_(x in W)j_x`. Since each typed letter's rank cost is at most 7j, the starting half-rank of W satisfies `r0<=r_init+7I` and the cost of W satisfies `T<=7J`. Thus whenever the even-slope divisor fails, any q>=3 repetitions of W necessarily obey the **exact integer inequality**

```text
           14*I + 28*J + 2*r_init >= 3*4^(J*(q-2)). (13)
```

This bounds the earliest *weighted inverse position* of a q-th power exponentially in its run-gap weight and q-2. Under the separate paper primitive-period valuation no-go, a shortest typed period containing j>1 always has the required divisor failure, giving an unconditional (within that still uncompiled paper composition) power-onset restriction for such words. It remains consistent with high-complexity aperiodic infinite symbolic paths and is not a whole-machine verdict.

For the **actual post-forced-F branch-29 signed feeder line** already formalized in [SignedFRunParity.lean](../agent18-429-root-invariants/SignedFRunParity.lean), `(u,D)=(48t,96t+18)` with `t≥1`, the initial half-rank is exactly `r_init=(6u+D)/2=192t+9`. Thus (13) specializes, for any repeated typed macro word with a non-even affine slope divisor, to the explicit root-parameter requirement

```text
   14*I + 28*J + 384*t + 18 >= 3*4^(J*(q-2)).       (14)
```

This is a uniform **necessary bound for signed-feeder descendants**, not a closure of the unknown branch-29 family. To promote it to a theorem about authentic positive BB429 ancestors still requires a source-to-actual-path quantifier and the existing signed precision lift.

The bounds are *necessary only*. Real paths face additional E/S guards, Bad leaves, and authentic-root ancestry constraints, so they may be impossible even at ranks above (10)–(12). For example, the nonempty legitimate signed prefix E2³ exists from `(u,D)=(183,32)`, `r0=565`: its paired inputs `(183,32)->(47,864)->(39,928)->(39,944)` satisfy the finite recurrence. E2⁴ fails from that same input at the next F divisibility. This is a concrete reminder that the quantitative no-go does **not** prohibit every finite cube.

## A strict finite slope-cone lemma (missing justification now made explicit)

For `W=(x_1,...,x_a)` with all `j_i>=1` and `s_i=4^(j_i)`, direct telescoping yields the *exact nonnegative coefficient gap*

```text
  M-1-3*A = sum_(i=1)^a [(s_i-4)*product_(k<i) s_k].  (4)
```

Indeed `M-1=sum_i (s_i-1)product_(k<i)s_k`, while `A=sum_i product_(k<i)s_k`. Thus `3A<=M-1`; it is **strict** as soon as any letter has j>1. Combining (2) and (4) shows, in a finite repeat with some F block,

```text
                 0 < 3*(u_1-u_0) < T.                 (5)
```

This is important: positivity of the D coordinate at only three finite boundaries, by itself, would *not* justify the slope-cone upper bound. The transfer-coefficient gap is the actual missing argument. At each intermediate paired phase i, subtraction of adjacent copies gives `4^j*s_(i+1)=s_i+T`. Starting from (5), positivity and `3*s_i<T` propagate to the next phase because `4^j>=4`. Each s_i is even from the paired E/S type guard in the two copies. Therefore T is even, and `v_i=s_i/2`, `K=T/2` are positive integers satisfying

```text
  4^(j_i)*v_(i+1) = v_i+K,       0<3*v_i<K.           (6)
```

The slopes return cyclically after one complete typed word, since its start/end are consecutive copy boundaries. This is the exact finite source of the strict cone used by the older triple-word valuation-packing argument; no infinite-state positivity has been smuggled into a finite theorem.

## Parity-free primitive gap-word exclusion from the new sharp packing theorem

The new **exact capacity theorem** [sharp four-adic signed packing](../../results/2026-11-28-sharp-signed-valuation-packing-agent22.md) upgrades the primitive-period inference, not just the numeric constant. Consider a typed word W whose *underlying positive-j word* is itself primitive and contains a letter j>1. When many copies force an integer-affine first-coordinate slope, the strict finite cone (4) supplies positive **integer** slopes s_i with `4^j_i*s_(i+1)=s_i+T`, `0<3*s_i<T`, and cyclic phase return after W. There is no need to infer evenness here. The sharp capacity theorem with K=T and `J=sum j_i` yields `15J<=2T<=14J` when `T>=15`, a contradiction. If T<15, the exact capacity enumerates all seven possible typed words with some j>1, each with `U(T)<J`; none can be a primitive integer-slope cycle. Consequently **no positive integer affine slope exists for a primitive j-period with a positive F-run**, even without the source E/S same-parity guard.

If the typed period consists of **two** copies of a primitive positive-j period with opposite E/S type, the word's full rank increment is larger (T can exceed 7J for the primitive subperiod); the parity-based half-rank reduction K=T/2 and the earlier 6J bound remain necessary. In both cases the full signed source-word-to-cyclic-slope Lean composition remains an open formal task. No BB429 whole-machine conclusion follows.

## Primitive typed-period no-go (paper composition)

If W is the **shortest valid typed period** and its underlying positive-j word has primitive gap period `(j_1,...,j_a)` containing j>1, the existing [ValuationCyclic.lean](ValuationCyclic.lean) and [ValuationEdges.lean](ValuationEdges.lean) prove that a cyclic positive integer slope sequence of the form (6) would require `K >= 6*t+1`, where `t=sum_(i=1)^a j_i`.

The type change is determined by j parity, so a shortest typed period is either one or two primitive gap periods. If it is one, `T=3*t+2e+4s` with `e+s=a<=t`, hence `K=T/2<=7*t/2<6*t+1`. If it is two, each gap letter appears once as E and once as S, so `T=6*t+6*a`, `K=3*(t+a)<=6*t`. In the doubled case the slope recurrence across one primitive gap period is an affine contraction `x -> alpha*x+beta` with `0<alpha<1`; a point fixed by its square is fixed by it. Thus the slopes are already periodic after the **primitive** gap period and the same valuation-packing contradiction applies.

**Paper corollary.** Under the source-certified E/S transition guards and parity rule, a genuine finite path cannot contain q>=3 repetitions of its shortest typed pair period containing j>1 whenever (1) holds. Formal Lean integration of the finite-cycle slope construction, especially the short-period reduction and source-to-original-machine adaptor, remains open. No claim of full Lean source acceptance is made here.

### Why minimality matters

The word `S2,S2,S2` has `M=4096,A=273,T=30`, so `A*T=2*(M-1)`: its three-letter *nonminimal* repeat passes the even-integer divisibility test. Reducing to the true typed core `S2` gives `M=16,A=1,T=10`, and `2*(M-1)=30` does *not* divide 10. It would be false to assert the naive parity divisor condition independently rules out every arbitrary nonminimal W; this is why the checker canonicalizes exact repeated typed words before applying the test.

## Reusable exact-integer pruner

[FinitePowerPruner.cjs](FinitePowerPruner.cjs) implements (1)-(3) with JavaScript BigInt, short-circuiting the power comparison against its finite threshold. Invocation:

```bash
node FinitePowerPruner.cjs E2 100 2
node FinitePowerPruner.cjs E2 100 5
node FinitePowerPruner.cjs S2,S2,S2 100 5
```

In the first example `M=16,A=1,T=8,H=38`, hence `16^3>76` and `30` does not divide `8`: five E2 repeats are impossible if begun at half-rank 100 with the required signed guards. In the second, the utility reduces the word to its one-letter typed core, counts 15 repeats, and rules them out with `30∤10`.

The test is **one-sided**: if its `excludedByExactNecessaryCondition` is false, it establishes nothing about a real path's existence or nonhalting. It is only a finite-word pruning subroutine; it does not replace the original #429 blank-root bridge or decide any six-state machine. Its direct algebraic condition requires no heuristic search. The stronger primitive-period all-word consequence is now kernel-certified at both the exact macro `Walk` level (`FinitePrimitiveNoGo.lean`) and the literal signed `SourceWalk` level (`SignedPrimitivePowerNoGo.lean`), accepted by narrow CI run `46160225088`. It is still not an authentic blank-root #429 theorem: the remaining source obligation is to derive the required repeated primitive `SourceWalk` blocks from every relevant original-machine ancestry, or exclude the aperiodic alternatives.

## Relevance and next proof edge

This bridges the already local-Lean-checked three-copy affine lemma to arbitrary finite powers and supplies the strict cone proof needed by the finite valuation argument. It can prune repeated segments of *aperiodic* signed-path candidates, rather than only excluding eventually periodic schedules. That finite cyclic slope construction and typed-period reduction are now formalized in `FiniteSlopeTransport.lean`, `FiniteSlopeCycle.lean`, `FiniteSlopePacking.lean`, `CyclicPrimitiveFinite.lean`, `SlopeCycleAdapter.lean`, and `FinitePrimitiveNoGo.lean`; the signed wrapper is `SignedPrimitivePowerNoGo.lean`. The decisive remaining edge is authentic original-machine coverage: show that every unresolved #429 ancestry either contains a repeated primitive source word long enough to trigger the bound or belongs to a separately controlled aperiodic class. Nonrepeating, high-complexity signed paths and the blank-root #429 decision remain unresolved.

# Candidate three-reset wall obstruction for all critical exponents n≥70

**Agent 28, 2026-11-04, mathematical research note. Conditional arithmetic derivation only.** This note proposes a substantial extension of the fully source-certified two-reset necessity at n≥30. The claimed absence of *exactly two* positive-depth resets has **not** yet been formalized as a complete Lean original-source theorem and must not be reported as certified. The required dyadic equalities are consistent with the locally Lean-certified [DefectTransport.lean](DefectTransport.lean) and [OneResetSourceBudget.lean](OneResetSourceBudget.lean). Independently verify all estimates and source hypotheses before promoting the argument.

## Proposed statement

In the original critical P1 odd inverse cone with root `(14·2^n−2n−16,3)`, for every natural `n≥70`, the affine wall `b=4(m+n)` cannot be reached by a history containing **exactly two positive-depth** `inverseAt` transitions, regardless of how many zero-depth inverses occur before, between, or after them. Together with the certified zero/one-reset theorem, this would imply every affine-wall witness must have at least three resets.

## Detailed arithmetic route

Use `P=2^n`, `x=n+2`, `K=7P−n−3`. Decompose a putative exactly-two-reset word into

```
upper^r ; reset^l1 ; upper^s ; reset^l2 ; upper^u,
l1≥2, l2≥2.
```

All costs are **lengths** in the source scalar grammar, so `m=r+l1+s+l2+u`. Write `R=2^r`, `L1=2^l1`, `S1=2^s`, `L2=2^l2`, `S2=2^u`.

The first upper/reset/upper prefix can be treated exactly as the already locally certified arbitrary one-reset word budget, without assuming a terminal wall. Its root, first reset and first upper suffix supply the bounds

```
R≤x, L1≤4x, S1≤6x,
m1=r+l1+s≤11x,
2^m1=R L1 S1≤24x^3.
```

At the intermediate odd hub introduce the positive defect representation `F+N1=7·2^(n−m1) C1`. The output of the first reset has `0<N1≤n+m1+1` and the subsequent upper suffix divides N1 by S1. Thus the intermediate remainder `N1'=N1/S1` obeys `0<N1'≤n+m1+1`.

For the **second reset**, put

```
M2=2(n+m1+2)−N1',   V2=2^(m1+1)−C1,
L2·D2 + M2=7·2^(n−m1) V2.
```

The bounds `0<M2≤2(n+m1+2)≤24x` follow from positivity of the first defect. The decisive quantitative estimate

```
2^m1 M2 ≤ (24x^3)(24x)=576x^4 < P
```

holds for every n≥70 (see exponential bound below). It implies `0<M2<2^(n−m1)`, hence the original 2-adic cancellation lemma forces `L2 | M2` and **`L2≤24x`**.

The second reset's output defect is

```
N2=n+m1+l2+1−M2/L2,
C2=2^(m1+l2)−V2,
F2+N2=7·2^(n−m1−l2) C2.
```

Because `L2≥4` and `M2≤2(n+m1+2)`, `0<N2≤n+m1+l2+1≤36x`. The final upper suffix satisfies

```
2^(m1+l2)·N2 ≤ (24x^3)(24x)(36x)=20736x^5 <P,
```

so `S2=2^u | N2` and **`S2≤36x`**. Therefore

```
m≤(11+24+36)x=71x,
2^m=R L1 S1 L2 S2≤20736x^5.
```

The already **source-certified** all-word wall-cost inequality is

```
7P ≤ n+4 + 2^m(3m+2n+4).
```

Since n+4≤P and x≥72, the putative two-reset wall yields

```
6P ≤ 2^m(3m+2n+4)
   ≤ (20736x^5)(216x)
   = 4,478,976 x^6
   < 6P,
```

an arithmetic contradiction.

The final growth bound `4,478,976(n+2)^6 <6·2^n` is true at n=70, with LHS exactly **623984373770747904** and RHS exactly **7083549724304467820544**. For n≥70, `72(n+3)≤73(n+2)` and `73^6<2·72^6`, so the LHS increases by a factor strictly below two when n increases by one; the RHS exactly doubles. This also implies the subordinate strict inequalities `576x^4<P` and `20736x^5<P`.

## Trust boundaries and falsifiers

- The generic input/output defect equations are fully local-Lean verified in [DefectTransport.lean](DefectTransport.lean). The all-word source cost threshold and one-reset budget are independently source-verified.
- The **novel two-reset composition is presently a handwritten derivation**, with no Lean statement yet quantifying all intermediate authentic source history forms. The two critical obligations are (i) automatically preserving the positive defect through the first upper suffix, including all natural subtraction boundaries, and (ii) composing both source resets into the exact inequality chain above.
- An exhaustive finite test, even for thousands of n, is insufficient to prove the universal inequality. The n≥70 exponential inequality is elementary but should be Lean-certified as part of a final proof.
- The restriction is specific to the **affine wall**. Exceptional `c=1` and high-cost even exits, and P1/BB(6) decisions, remain open.
- A potential counterexample would be an exact source `OddCone` upper/reset/upper/reset/upper witness with `n≥70` reaching `b=4(m+n)`, or a valid witness violating one of the stated preservation bounds. Reproduce such a witness using the original `inverseAt` source and report it rather than assuming this manuscript is correct.

**Next action:** turn these quantified inequalities into `OneResetTwoResetBudget.lean` importing `DefectTransport`, `OneResetSourceBudget`, and `OddWordCost`, then connect original `UpperTail` and `OddCone` as in `OneResetCount.lean` and run manually triggered original-source CI. This route avoids a new residue sieve.

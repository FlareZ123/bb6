# Iterated dyadic defect transport for the critical P1 inverse grammar

**Agent 28, 2026-11-04.** Intermediate exact algebraic lemma locally kernel-verified in Lean 4.36.0-rc2 (`DefectTransport.lean`), standard axioms `[propext, Quot.sound]`. Full all-word `OddCone` transport and uniform iteration are not yet established. This is a mechanism for studying histories with **two or more positive-depth resets** after the source-verified one-reset exclusion.

## Notation and exact source connection

Use the already original-source-certified coordinates [OddWordSourceBridge.lean](OddWordSourceBridge.lean). Fix n and P=2^n, K=7P−n−3. Any genuine odd inverse word has variables `D≥0`, total inverse cost `m`, and left-shifted mass `F=K−D−m+2=(b+12)/2`; its next odd inverse length `l=t+1≥1` obeys

```
2^l D' + m = K + D,        m'=m+l.
```

In a **low-cost** segment with m≤n, introduce a *defect representation*:

```
F + N = 7·2^(n−m)·C,      N>0,  C odd, 0<C<2^m.
```

At the genuine initial precursor (D,m)=(1,0), this holds with C=1,N=n+2. Note `C<2^m` is not strict at m=0; the uniform useful bound is `0<C<2^(m+1)`, and `C=1=2^m` initially. After a reset, `C` grows but remains odd and below `2^m` when l≥2, provided the prior C≤2^m. **Any inductive statement must keep this boundary case explicit.**

An upper step (`l=1`) has `F'=F/2`, so if m+1≤n and 2 divides N, it preserves `C'=C`, `N'=N/2`. Exact source admissibility requires more than these displayed scalar conditions.

For a reset (`l≥2`), define

```
B=2^m,  L=2^l,
M=2(n+m+2)−N,  V=2B−C.
```

**Exact input identity:**

```
L·D' + M = 7·2^(n−m)·V.
```

If `0<M<2^(n−m)` and L divides the right side, [OneResetTwoAdic.lean](OneResetTwoAdic.lean) forces `L | M` and `L≤M`. This bound is genuinely structural; it excludes arbitrary long resets while the dyadic defect remains smaller than its ambient power of two.

Writing `M=Lh`, assuming `m+l≤n`, and setting

```
C'=2^(m+l)−V,  N'=n+m+l+1−h,
```

the **exact output identity** is

```
F' + N' = 7·2^(n−m−l)·C'.
```

Both input/output identities have complete local Lean proofs in [DefectTransport.lean](DefectTransport.lean). They are uniformly quantified in *every* n,m and reset length under the displayed exact equations, and use no finite simulation or source mocks.

## Quantitative implication under a certified low-cost regime

Suppose along an individual sequence the defect maintains `0<N≤n+m+2` and `m≤n`, and every reset satisfies `0<M<2^(n−m)`. Then `0<M≤2(n+m+2)`, every reset length has `2^l≤2(n+m+2)`, and any intervening upper run of length s has `2^s≤N≤n+m+2` provided the upper steps preserve positive N. Thus a **complete upper/reset block** contributes a multiplicative cost factor at most

```
2^(s+l) ≤ 2(n+m+2)^2 ≤ 8(n+1)^2.
```

Iterating this conditional estimate suggests a lower bound on the number of positive-depth resets of any possible wall-reaching history. A *fixed* reset count k would force polynomial total `2^m`, in tension with the independently source-proved wall necessity `2^(n−m)<n`. The induction must prove its hypotheses, handle the transition where m approaches n, and account for the final upper segment. **No unconditional all-k reset-count lower bound is yet claimed.**

The one-reset case was handled directly with all required remainder inequalities in [OneResetSourceBudget.lean](OneResetSourceBudget.lean), and the source-connected wall exclusion passed [manual CI 41747017916](https://github.com/FlareZ123/bb6/actions/runs/41747017916). For two or more resets the newly proved generic defect transport is a potential organizing invariant.

## Immediate next proof obligations

- Derive the defect representation and positivity bounds inductively for every authentic `OddCone` word whose cost stays well below n; distinguish the seed case C=2^m from later states
- Prove an explicit bound on the number of reset blocks needed to reach m within O(log n) of n, by combining the per-block polynomial growth bound with the source-certified wall threshold
- Test whether the necessary bounds remain useful at genuinely reachable blank histories, separately from synthetic predecessor cones
- Source-audit the stronger [OneResetCount.lean](OneResetCount.lean) original-grammar two-reset necessity before citing it as formally certified

No P1 nonhalting proof, BB(6) bound or academic novelty determination follows from the present conditional estimate.

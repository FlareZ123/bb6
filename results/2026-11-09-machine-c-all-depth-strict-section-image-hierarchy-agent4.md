# Infinite strict image hierarchy for the original Machine C first-return section

**Agent 4, 9 November 2026. Original-source Lean theorem, all finite depths.**

The standard Machine C two-counter first-return map `F=BB6.Agent46.secNext` has a strictly decreasing sequence of successful-return images **at every depth**, with an explicit positive-density cylinder in every difference. The same cylinders are absent from the *authentic* blank-origin section orbit at all times. The statements quantify over every natural depth and every natural cylinder parameter, without an arithmetic cutoff or a finite simulation horizon.

**Proof status:** Lean 4.36.0-rc2, compiled with unmodified original Machine C source definitions and their original-source inverse bridge. [Successful manual source CI 42602556589](https://github.com/FlareZ123/bb6/actions/runs/42602556589); previous [strict hierarchy CI 42602193578](https://github.com/FlareZ123/bb6/actions/runs/42602193578). The new source theorem files are [CFourHierarchy.lean](../im-results/agent4-c-four-step-image/CFourHierarchy.lean) and [CAllDepthBlank.lean](../im-results/agent4-c-four-step-image/CAllDepthBlank.lean). All theorems are ordinary Lean proofs with no `sorryAx`.

## Exact mathematical statement

For natural `n`, let `I_n` be the image of `n` successful iterations of the original partial first-return map `F`, with **arbitrary initial counter source**:

```
I_n = { p : there exists q such that run F n (some q) = some p }.
```

For every `r,s,t >= 0`, define

```
X_r(s) = 8*s + 7 + 4*r,
Y_r(t) = 2^r * (16*t + 44) - 2.
```

**Theorem (all-depth exact separation).**

```
forall r,s,t:
  (X_r(s), Y_r(t)) in I_(r+2) \ I_(r+3).
```

Consequently **`I_(r+2) strictly contains I_(r+3)` for every natural `r`**. Since the pairs above occupy one complete residue lattice `x mod8` and `y mod2^(r+4)` beyond fixed lower coordinate boundaries, this yields the positive-density bound

```
lower asymptotic density(I_(r+2) \ I_(r+3)) >= 2^(-r-7).
```

The Lean theorem `BB6.Agent4Four.cone_strict_image` is stronger than the concrete witness formula: it handles a recursively defined lifted cone `Cone r x y` for arbitrary targets. The theorems `each_cone_has_cylinder` and `all_image_depths_strict` supply the infinite positive-density family and strictly decreasing image hierarchy.

**Theorem (genuine blank-origin nonreachability).** For every natural `r,s,t,time`,

```
run F time (some (5,1)) != some (X_r(s),Y_r(t)).
```

The stronger `cone_blank_unreachable_all_depths` applies to every target in the recursive cone, and `blank_excludes_all_depth_cylinders` applies it to the explicit lattice. This has been original-source kernel-checked at *unbounded* depth and time.

## Source-level proof

The already source-certified Agent 34 strict two-versus-three image cone states that every target `(a,k)` with `k>=34`, `k%16=10`, and `(a+k)%8=1` has exactly two consecutive genuine first-return predecessors but no three. The authentic `section_preimage_all_iff` theorem and Agent 4's `only_direct_mod4_one` establish that if a target `(x,y)` has `y>=6`, `y` even, and `(x+y)%4=1`, then its **only** possible direct section predecessor is

```
(x+y-2, (y-2)/2),
```

and the original source map indeed takes this predecessor to `(x,y)`.

Fix `r,s,t` and set `B=16*t+44`. The explicit genuine direct-section chain of length `r` uses, for `0<=i<=r`,

```
k_i = 2^i * B - 2,
a_i = 8*s+7+4*i + 2*(2^r-2^i)*B.
```

The initial state `(a_0,k_0)` satisfies the Agent 34 sharp `I_2\I_3` sector, because `k_0=16*t+42` and `a_0%8=7`. Every consecutive step is an original direct source return `F(a_i,k_i)=some(a_(i+1),k_(i+1))`, with all input branch guards satisfied. Each child has even right coordinate at least six and coordinate sum `1 mod4`, forcing exactly that preceding state as its sole possible parent.

The general lifting implication therefore holds:

```
p in I_n \ I_(n+1),
F(p) = some q,
q has unique predecessor p
  ==> q in I_(n+1) \ I_(n+2).
```

Induct from the Agent 34 sector to obtain the all-depth image separation. The same unique-inverse argument pulls any supposed authentic blank hit back to the original Agent 34 blank-unreachable cone. This proves the all-time blank theorem independently of the step count.

### Exact density of the disjoint lifted bands

For each fixed `r`, the explicit lattice has natural density exactly `2^(-r-7)` in growing square coordinate boxes. The `r`-bands are pairwise disjoint, since

```
v_2(Y_r(t)+2)=r+2
```

for all `t` (the odd factor is `4*t+11`). Their union consequently has asymptotic natural density

```
sum(r=0..infinity) 2^(-r-7) = 1/64.
```

The interchange of the limit and series follows from the geometric tail bound on the number of lattice points in any `[0,N)^2` square; the number of nonempty `r` bands is only `O(log N)`. This is a **paper counting corollary** of the kernel-certified per-depth inclusion, and is not claimed as a separate Lean kernel theorem.

All these bands lie inside `I_2` and are therefore different from the already known one-return missing-image region. Together, they yield an explicitly described 1/64-density subset of blank-unreachable section states *that admit at least two genuine arbitrary-source predecessors*.

## Relationship to genuine Machine C halting gates

The exact high-family stopping equation is `k+j+3*m+5=2^(2*m+2)*(j+3)`. Pulling back the strict image hierarchy gives all-time genuine blank-origin exclusions for any stopping pair lying in the proven lifted bands.

**Important overlap audit.** The earlier `r=1` high-family residue exclusion `m>=3, j%4=0, m%4=3, (j+3*m+5)%32=10` is a **special case of Agent 19's already source-certified all-depth dyadic exclusion**, at their inverse depth `n=1`. In fact the `r`-th lifted band high-stop pullback is covered by that older theorem whenever `r+4<=2*m+2`. These high-depth bands should not be counted as newly removed high stopping parameters.

**Two distinct low-stopping-depth `m=1` discoveries escape the older Agent 19 dyadic predicate** because that predicate permits only `n=0` when `m=1`. For every `q>=0` the original high-family equation and true blank nonreachability hold for

```
m=1, j=64*q+26,    (x,k)=(128*q+55, 960*q+430).
m=1, j=256*q+266, (x,k)=(512*q+535,3840*q+4030).
```

The first is the `r=2` strictly three/four-depth lifted source band, proved in [CNewM1.lean](../im-results/agent4-c-four-step-image/CNewM1.lean) and [successful original-source Lean CI 42604195908](https://github.com/FlareZ123/bb6/actions/runs/42604195908). The second is the disjoint `r=4` source band, proved in [CNewM1Depth4.lean](../im-results/agent4-c-four-step-image/CNewM1Depth4.lean). Its full original-source CI status is recorded in the [research dossier](../im-results/agent4-c-four-step-image/README.md). Each proof is unbounded in `q` and section-return time. The candidate index families are disjoint since their `j mod64` classes are 26 and 10. Together they remove two explicit arithmetic progressions from actual Machine C blank-reachable stopping inputs, with density `1/64+1/256=5/256` *within the one-dimensional `m=1` parameter ray*, subject to overlap with other previously proved restrictions.

The earlier Agent 29 exact right-four m=1 tower is a discrete sequence, and Agent 19's all-depth dyadic predicate cannot eliminate either new progression. The full strongest merged `highAllowedValSixFull` predicate and all other independent sieves have **not yet received a separate all-parameter Lean admission proof** for these progressions. Therefore no exclusive new parameter-count claim beyond the explicit source-verified absence and Agent 19 overlap audit is made.

## What remains unresolved

The decreasing image hierarchy concerns *arbitrary source* return images, rather than the reachability of every possible halting state from the single blank source. The positive-density removed bands are not sufficient to establish Machine C nonhalting. Machine C's authentic blank-section root decision, the other six-state holdouts, a universal BB(6) upper bound, and the exact BB(6) value are still open.

The separate [exact eventual fourth-image density calculation](../im-results/agent4-c-four-step-image/README.md) reports `57,236,403/134,217,728`, derived by paper arithmetic and exhaustive finite integer computation; its numeric density has not independently received a Lean source/kernel counting theorem. The proof statuses of that calculation and the unbounded strict-image hierarchy must remain distinct.

**Related original proof foundations:** Agent 34 [three-return inverse obstruction](../im-results/agent34-c-degree-profile/ThreeConeSource.lean) and [two-step genuine predecessor witnesses](../im-results/agent34-c-degree-profile/ThreeConeProper.lean); Agent 3 [complete original section predecessor iff](../im-results/agent3-c-bounce-inverse/SectionAllInverse.lean); Agent 4 [unique direct predecessor](../im-results/agent4-c-three-ancestry/CThreeArithmetic.lean). All public novelty statements concern the concrete new theorem and its induction, with the base strict two-versus-three image result correctly credited to Agent 34.

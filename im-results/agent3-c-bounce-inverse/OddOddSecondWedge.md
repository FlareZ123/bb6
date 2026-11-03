# Machine C two-stage odd–odd backward obstruction and second high stopping family

**Agent 3, 2026-11-03 18:22 UTC.** [Original unmodified source CI run 41692615880](https://github.com/FlareZ123/bb6/actions/runs/41692615880) **SUCCESS**. Its Lean 4.36.0-rc2 job [126114812306](https://github.com/FlareZ123/bb6/actions/runs/41692615880/job/126114812306) proves all three theorems in [OddOddSecondWedge.lean](./OddOddSecondWedge.lean) under the actual original Machine C definitions, with axiom audits exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. This is an intermediate family-exclusion result. Machine C and BB(6) remain open.

## First uniform backward cone

Let `a,k` be arbitrary naturals satisfying

```
a%8=4, k%8=3, k>=5, (a+k+1)%16=8, a+k>=23.
```

The original-source [`odd_seven_parent_equations`](./OddSevenSliver.lean) forces the *sole* incoming source `(b,c)` to satisfy

```
a+k=2*b+5, a+3*k=4*c+9,
c>=5, c%2=1, (b+c)%4=2.
```

But [`blank_section_odd_image`](../agent3-c-odd-image/Agent3CImage.lean) proves that every post-initial blank-orbit return whose second counter is odd and at least five has counter sum congruent to **0 or 3 mod 4**. The initial state `(5,1)` also fails `c>=5`. Therefore no real source predecessor `(b,c)` can occur in the blank orbit. The new `odd_seven_four_three_unreachable` certifies the whole two-dimensional cone, with no simulation-time cutoff.

## Pullback through the valuation-two odd–odd inverse

From [OddOddWedge.lean](./OddOddWedge.lean) and [OddOddOrbit.lean](./OddOddOrbit.lean), every target `(x,y)` with `x,y` odd, `y>=5` and `(x+y)%8=4` has exactly one genuine predecessor:

```
A=(x+y-4)/2, K=(x+3*y-10)/4.
```

The theorem `oddodd_second_wedge_unreachable` excludes all such targets satisfying `A%8=4`, `K%8=3`, `(A+K+1)%16=8`, and `A+K>=23`. The proof uses the full blank-orbit reachability equivalence, then the preceding even/odd cone. No quotient assumption, finite bound on `x,y`, or guessed inverse branch is involved.

## New authentic high stopping family

The root halting section condition [Agent 15](../agent15-c-halting/SectionParam.lean) includes

```
k+j+3*m+5 = 2^(2*m+2)*(j+3).
```

The new source-proved theorem `high_halt_oddodd_second_64_unreachable` gives, for **all** natural j,m,k,time,

```
m>=4, m%4=0, (j+49*m)%64=62,
and k+j+3*m+5=2^(2*m+2)*(j+3)
  ==> run secNext time (some (5,1)) != some (2*j+3,k).
```

The proof establishes the target height `k>=200` by an induction-checked exponential inequality, checks the odd–odd inverse guard modulo 8, and proves the parent's four modular/size constraints by the source's exact halting equation modulo 64. This is disjoint in `m%4` from the earlier [first odd–odd high stopping family](./OddOddWedge.md) with `m%4=2`.

Example: `m=4, j=58, k=62389`. The actual stopping target is `(119,62389)`; its sole parent is `(31252,46819)`; that parent's sole parent is `(39033,42925)`, an impossible blank-orbit state because `(39033+42925)%4=2` with odd second counter `42925>=5`. These are real original-section source edges, not abstract graph edges.

## Quotient comparison and limits

Independent reproductions of [B8/M32](../../tools/agent43_c32_certificate.py) and [mixed96](../agent41-mixed96/mixed96.cpp) reproduce their published numerical graph sizes (31,570/189,834 and 260,672/2,022,544 reached vertices/processed edges). In B8/M32, all **4** projected target cells of this new congruence family are **present**, while its **8** canonical-parent projected cells are **absent**. In mixed96, all **12** target cells are present, while all **24** parent cells are absent. The quotient counts and residue projections are **computational cross-checks**, not ingredients of the Lean proof; mixed96 full closure has not been checked in the Lean kernel. The source-certified two-stage inverse is what justifies the authentic blank exclusion.

This strengthens the obstacle beyond direct target nonmembership in either particular quotient. No claim of novelty relative to every unexamined prior theorem, resolution of Machine C's full stopping locus, or exact BB(6) value is made. Keep both this note and [source Lean file](./OddOddSecondWedge.lean) in `im-results/` until independent novelty review and a publishable synthesis are justified.

# All-time asynchronous disjointness of the two rooted S-counter orbits

Agent 9, 2026-11-02. **A new source-derived, Lean-kernel-checked structural theorem for two known rooted BB(6) holdouts. Intermediate; no machine halting decision or BB(6) value.**

## Two different rooted starts of the same unrooted six-state table

The DeepMind Cryptids six-state table `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB` has two distinct designated blank roots. Its original A-root enters S(b=125,c=3), so q=b+16=141. The reflected/permuted table `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---` has its rooted A-blank entry, as proved upstream and independently checked by Agents 3 and 10 in `im-results/agent10-st-family/`, corresponding to original S-table blank start B and S(b=1,c=3), so q=17.

For the q-only accelerated S counter `f`, define

```
f(q) = 4*(q/3)       if q%3=0,
       4*(q/3)-3     if q%3=1,
       4*(q/3)+1     if q%3=2.
```

Natural division applies; q>=16 is preserved and in fact q grows strictly.

**New all-time theorem:**

```
∀ a b : Nat, f^[a](17) ≠ f^[b](141).
```

The quantifiers allow **any different iteration counts** a and b. In particular, the *first* S episodes of the two original rooted machines have no common q counter at any pair of times while their real accelerated orbits remain in the S phase. The mathematical q-only extension is defined even if the physical machine has already left S; the theorem neither excludes an eventual S-to-T transfer nor establishes globally disjoint raw-machine configurations after arbitrary phase changes.

## Finite base cases plus a universal separation invariant

Every `q>=16` satisfies the source-derived inequalities

```
4q <= 3f(q)+13,     3f(q) <= 4q.
```

Therefore the gap of 14 is **forward-preserved**:

```
16 <= x, 16 <= y, x+14 <= y  ==>  f(x)+14 <= f(y).
```

Both q orbits increase strictly. The two finite exact calculations

```
f^[8](17)=125,       f^[9](17)=165
```

give a global dichotomy: for every k, either `f^[k](17)+14<=141` (k<=8) or `141+14<=f^[k](17)` (k>=9). Hence any time-shift comparison between the first rooted orbit and the second is already separated by >=14 before common forward iterates are applied.

If a>=b, write a=(a-b)+b, apply the dichotomy at k=a-b, and preserve its gap for b common steps. If b>a, compare 17 with f^[b-a](141)>=141 before a common steps. Thus equality is impossible for all two natural times, by elementary induction and exact arithmetic.

This method is useful more generally: any two counter orbits with a uniform forward separation band and finite transition through that band can be certified asynchronously noncoalescing via finitely many initial checks.

## Formal proof and provenance

The complete source is [`SDisjoint.lean`](./SDisjoint.lean), importing prior locally checked [`SExponential.lean`](./SExponential.lean). All facts above, including iterated map semigroup, monotonicity, 14-gap preservation, 8- and 9-step evaluation, and two-time conclusion, compile in Lean 4.36.0-rc2. Final axiom audit:

```
'BB6.Agent9SDisjoint.roots_ne' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no unproved constants, no presumed root-merging equivalence. Before GitHub upload local source SHA-256 `36667e52c6850e3e6b35acdff08f70d9a74322ea619b3c8ca5595c911c3fe8e8`, using `import SExponential` compiled to `SExponential.olean`. The Lean proof is entirely standalone arithmetic of the same published S q map, while authenticated raw-machine entry and original semantics are separate earlier source facts. An unmodified upstream-source integration CI chain has **not yet been run for this theorem**, so do not claim original-source-certified raw-machine exclusion.

**Research scope:** This structural disjointness is potentially valuable for rooted holdout classification, avoiding unsupported fusion of the two designated starts. It does not imply that either initial S episode lasts forever, and alone cannot settle either six-state machine or BB(6). Record only in `im-results/` unless integrated into a substantive machine decision.

## Strengthened quantitative bound and two-dimensional surviving-phase semantics

The later [`SQuantitative.lean`](./SQuantitative.lean) verifies a sharper all-time theorem for every pair of iteration counts:

```
iterQ 17 a + (16 + min a b) ≤ iterQ 141 b
  ∨
iterQ 141 b + (16 + min a b) ≤ iterQ 17 a.
```

The **16-unit constant is optimal**, with equality at `a=8,b=0`: 141−125=16. The general kernel-checked lemma `nextQ_gap_growth` establishes that a difference of at least 14 between source q counters grows by **at least one unit per common subsequent iteration**. Hence a 16-unit separation at the time-alignment boundary becomes `16+min(a,b)` after shared steps.

[`SPhysicalPhase.lean`](./SPhysicalPhase.lean) encodes the exact S-phase height updates as a partial map on `(q,c)`, where the only failure means **transfer to T**. Lean establishes that every surviving phase has the q-only iterated projection, and proves `surviving_roots_distance` for actual surviving S-phase trajectories, with the same lower bound `16+min(a,b)` on their q difference. Both final theorems compiled locally in Lean 4.36.0-rc2 with only `[propext, Quot.sound]` and no sorry; as above, a separate unmodified-upstream semantic import check remains open.

The stronger result rules out even a near-coincidence at any large pair of surviving S epochs. It still does not decide whether the first S episode ever transfers to T, nor whether the two full raw machines eventually have related configurations.

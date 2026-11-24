# Root-history exclusions for #623 synchronization counterexamples

**Agent 41, 2026-11-24. Intermediate result; not a nonhalting proof.**

This note separates two different source-authentic counterexample families and records what the blank-root history already excludes.

## 1. The stronger joint synchronization + square-gap family is excluded by parity

Agent 1's [JointSyncSquareGapNonclosure.md](../../agent1-623-sync-only/JointSyncSquareGapNonclosure.md) constructs, for every depth ell >= 30, an original-source LE-to-LE transition with the same S-window cut. The source synchronizes both full carry rectangles and has a strong old-ray square-gap; the target loses synchronization and even the factor-one square-gap.

For that family, q is even, the drain block is b=q+2 (even), and the exact drain digit normal form uses
- L congruent to b modulo 2;
- D = L - 2*n2.

Thus L and D are even. The family chooses
`c = 9q + 9D + 8R + 34 + 5P`,
where P is a power of 3 and hence odd. Therefore c is odd, and both the source first counter `4q+c` and target first counter `3q+c-2-D` are odd.

The original-source theorem `run_preserves_even` in [Parity623Source.lean](../../agent49-parity623/Parity623Source.lean) proves that every surviving blank-origin section state has an even first counter. Consequently, **every source and target in this stronger all-depth family is excluded from the authentic blank-root orbit**.

Scope matters: this parity argument does **not** exclude the earlier cone-only family in [InfiniteConeSyncNonclosure.md](../../agent1-623-sync-only/InfiniteConeSyncNonclosure.md), whose construction uses c=20*ell and has even first counter. Nor does parity alone exclude the separate two-call witness below.

## 2. The two-call witness lies in a skipped root-mass interval

Agent 1's separate source-authentic transition is
`D(4388,1094) -> D(3284,3310)`.
Its endpoint masses are exactly
- source: 4388+1094 = **5482**;
- target: 3284+3310 = **6594**.

A source-faithful BigInt replay of the original high-level rules gives the adjacent blank-root prefix anchors
- index 23: `D(1228,4156)`, mass **5384**;
- index 24: `D(2924,3705)`, mass **6629**.

Agent 49's original-source theorem `next_strict_mass` proves that every successful high-level transition, from every input state, increases mass by at least 7. Thus the mass of every surviving blank-root iterate is strictly increasing. Once the two adjacent anchors are kernel-certified, they imply the global root-history exclusion
[
orall n,quad run(n)=D(a_n,d_n) Longrightarrowa_n+d_nle5384 lor 6629le a_n+d_n.
]
Both endpoints of the two-call witness lie strictly inside (5384,6629), so neither can occur on the blank-root orbit.

The exact source-imported proof is drafted in [RootMassGapSource.lean](RootMassGapSource.lean). It imports the unmodified pinned Cryptids transition via Agent49ParitySource and proves:
1. mass monotonicity between arbitrary surviving run indices from `next_strict_mass`;
2. exact source-run anchors at indices 23 and 24 by kernel computation;
3. the skipped mass interval and exclusion of both witness endpoints.

**Verification status:** the exact root anchors and the combined interval theorem remain pending the next pinned-source CI run. The finite source-faithful replay and the existing source theorem motivate the proof, but they are not substitutes for that import check.

## 3. What this does and does not establish

The two root-history filters above exclude the *stronger joint sync/square-gap family* and the *two-call witness*. They do not exclude the earlier even-first-counter cone-only family, prove that the authentic root synchronizes forever, or close any halting branch of #623. A root-restricted synchronization product must retain explicit history conditions and must not generalize from arbitrary source-cone states.

No claim about BB(6)'s exact value follows.

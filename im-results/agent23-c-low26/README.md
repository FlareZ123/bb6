# An unbounded five-link inverse obstruction in Machine C

**Agent 23, 6 November 2026.** This is a source-certified intermediate Machine C result. It does not decide whether Machine C halts or determine BB(6).

## Exact original-blank theorem

Let `secNext` be the **unmodified** Machine C two-counter section map from `im-results/agent46-c-jump/FastSectionDef.lean`. Define `CReach a k` as reachability of `(a,k)` at any section time from the actual blank-entry section `(5,1)`, as in `Agent3COrbitIff.lean`.

The Lean theorem [`blank_no_rectangle`](C26Rectangle.lean) proves, for **all** natural `u,v` with `v≥1`,

```text
¬ CReach (64*u+1) (256*v+26).
```

This is a two-dimensional, infinite cylinder, without search depth, numeric fuel, or finite parameter restrictions. The proof reverses the following five **source-exact** section edges:

```text
(64u+1,         256v+26)
   <- (64u+256v+25,  128v+12)    even-right exact inverse
   <- (64u+384v+35,   64v+5)     even-right exact inverse
   <- (32u+224v+18, 16u+144v+10) odd/odd exact inverse
   <- (48u+368v+26,  8u+72v+4)  even-right exact inverse
   <- (56u+440v+28,  4u+36v+1)  even-right exact inverse
```

The displayed arrows point from a section target to its uniquely forced original-blank predecessor. Every even-right edge uses `BB6.Agent46.six_even_right_blank_reach_iff` from Agent24's unchanged source-certified `EvenRightSixOrbit.lean`. The middle odd/odd edge uses `BB6.Agent3.oddodd_lowval_blank_reach_iff` from Agent3's `OddOddLowVal.lean`. Their hypotheses are proved arithmetically for all `u≥0,v≥1`.

The final state has odd right counter `4u+36v+1 ≥ 37`, while its counter sum `60u+476v+29` is congruent to **1 modulo 4**. Agent3's original `blank_section_odd_image` proves that a post-initial section output with odd right counter at least five must instead have sum congruent to **0 or 3 modulo 4**. The final state is distinct from the true initial state `(5,1)`, so this contradiction closes every possible blank-rooted trajectory.

## Stopping-family consequences

The full original-source [`LowC26.lean`](LowC26.lean) proves the previously unexcluded first stopping parameter class

```text
m % 256 = 246
k + 3*m + 4 = 2^(2*m+3)
--------------------------------
¬ CReach 1 k
```

because `k % 256 = 26` and `k ≥ 282`. This proof was completed independently using the narrower `(1,256v+26)` instance, and remains a standalone verified corollary.

The source-certified [`C26High.lean`](C26High.lean) proves a coupled, two-parameter obstruction for the **high** stopping family:

```text
j % 32 = 31
(j + 3*m + 5) % 256 = 230
k + j + 3*m + 5 = 2^(2*m+2)*(j+3)
----------------------------------
¬ CReach (2*j+3) k
```

The congruences force `m≥22`, make the high right-hand power divisible by 256, and imply `(2j+3)%64=1`, `k%256=26`, and `k≥256`. Thus the supposed high stopping source falls inside the forbidden rectangle. In conventional pairs of residues modulo 256, the eight excluded `(j,m)` pairs are `(31,150)`, `(63,54)`, `(95,214)`, `(127,118)`, `(159,22)`, `(191,182)`, `(223,86)`, and `(255,246)`.

[`JointC26.lean`](JointC26.lean) incorporates these two exclusions into the current exact **time-free** blank-halting iff of Agent19's `JointFiveSieve.lean`. It tightens the low admissibility predicate with `m%256≠246` and the high admissibility predicate with `¬(j%32=31 ∧ (j+3*m+5)%256=230)`, retaining exact `mixedFiveFastRootDecision` for each individual parameter. Both remaining existential domains are infinite. This is a lossless arithmetical reduction, not a global halting decision.

## Verification and research boundary

The original CLine, jump, bounce, true section, exact inverses, and genuine blank-orbit image invariant are compiled unchanged by [the manual source workflow](../../.github/workflows/agent23-c-low26.yml), with Lean **4.36.0-rc2**. The widened rectangle and high parameter theorem passed [CI run 42211247750](https://github.com/FlareZ123/bb6/actions/runs/42211247750), with `#print axioms` recording only `propext`, `Classical.choice`, and `Quot.sound`, and no `sorryAx`. The standalone low theorem passed [run 42209795855](https://github.com/FlareZ123/bb6/actions/runs/42209795855). The combined exact-iff theorem is checked separately by [the joint source workflow](../../.github/workflows/agent23-c26-joint.yml).

The originality claim is limited to the shared repository's currently inspected source results. These theorems combine established original-source inverse maps with a newly identified symbolic five-link sector. External prior-art comparison is incomplete. They supply a new infinite excluded low family and a coupled infinite high family, and no upper bound for BB(6).

# F321: exact terminal-word guards and density-zero dangerous anchors

## Result and scope

Use the original F321 counter relation `CounterReach` on nonnegative pairs (a,d), with terminal gate a=d+1. A prepared anchor is (R,c) with c=1 or 2. Call it dangerous if some finite sequence of High/Far steps reaches a terminal gate without an intervening reset. We prove:

1. An exact arithmetic criterion for an arbitrary finite terminal word, including every source guard.
2. Equivalence of authentic root halting to reachability of an anchor satisfying that criterion.
3. A cutoff-free bound: for k≥2 there are at most **2 Fib(k+12)** distinct dangerous anchors with R≤2^k. In particular, for j≥1 the number with R≤4^j is at most 288·3^j, so the set has natural density zero.

These statements do not prove F321 nonhalting. The authentic orbit could meet a sparse dangerous set. This does not close Raw132 or establish the global Busy Beaver upper bound.

## Exact arithmetic

Put x=a+d+5, v=d+3. The High and Far updates are respectively

- H: (x,v) → (x+1,2v), permitted if x≥2v+1;
- F: (x,v) → (x+6,4v−3x+6), permitted if 3x≤4v+2.

The terminal gate is x=2v. For a chronological word w, define (P,Q,L,K) recursively from the tail: the empty word gives (1,1,0,0); prepending H gives (2P,Q,L+1,K); prepending F gives (4P,Q+6P,L+6,K+(3L+24)P). Here P=2^S, where S counts H with cost 1 and F with cost 2; Q>0, Q+1≤2P. For terminal scale T=t+3 the endpoint equations are

```
x+L = 2T
Q T = P v + K.
```

For each nonempty suffix u, use its own P,Q,L,K. Its required guard is equivalent to an integer lower bound on T:

| Head | positive slope | nonnegative demand |
|---|---:|---:|
| H | 2(P−Q) | max(0,P(L+1)−2K) |
| F | 4Q−6P | max(0,4K−P(3L+2)) |

Let exactMin(w) be the maximum over the ceilings of demand/slope, or 0 for the empty word. Then the two endpoint equations and T≥exactMin(w) are necessary and sufficient for the source-guarded terminal run, starting from a nonnegative state.

After an initial H^h from (R,c), v=2^h(c+3) and x=R+c+5+h. The remaining suffix must be empty or start with F if h is maximal. The exact criterion is

```
N = P 2^h(c+3) + K
Q | N,    T = N/Q ≥ 3
R+c+h+5+L = 2T
T ≥ exactMin(w)
2^h(c+3)+L+2 ≤ 2T.
```

The last inequality ensures a nonnegative first counter at the end of the initial High run. There is no word-length cutoff. Every authentic root terminal run decomposes at its last small-second anchor and yields this criterion, and every reachable anchor satisfying it yields an authentic terminal run.

For fixed w,c, sufficiently large h requires only the displayed divisibility test for existence of a prepared R; any period p satisfying 2^p≡1 (mod Q) gives a period of that test. In particular, for a single Far followed by H^b, a terminal suffix H^h F H^b from c∈{1,2}, b>0 must satisfy

```
2^b < (3b+24) 6^floor(h/b).
```

This removes an unbounded region of the two-length parameter space.

## Why the count holds for *all* word lengths

For two runs following the same guarded H/F word, their counter-sum difference remains constant. If the run with the smaller sum has the larger second counter by ε, after a common suffix of cost S the second-counter gap is at least 2^S ε. The first Far after H^h creates a gap at least three times the difference between the two initial R values. The Far guard at that point bounds the counter sum plus five by 7·2^h.

The kernel proves that a Far-headed prefix of cost at least h+6 can therefore belong to at most one R for fixed h,c: otherwise the amplified gap exceeds the available sum (each letter increases the sum by at most three times its digit cost). A complete shorter terminal suffix likewise determines R uniquely by the endpoint equations. Truncate every long suffix at its first crossing of cost h+6: the overshoot is at most one. Every dangerous anchor with R≤2^k consequently has a code (h,c,u) with h≤k and S(u)≤h+7, and each code decodes to at most one anchor.

The number of H/F words of cost at most m is Fib(m+3)−1, since the two letters have costs one and two. Summing over h and both c values gives the stronger exact cover-length expression

```
2 (Fib(k+12) − Fib(11) − (k+1))
```

and hence the stated bound. The Lean theorem works with an arbitrary finite Nodup list of dangerous pairs, without assuming decidability or finite maximal duration of all H/F runs. The integer power-four corollary follows from Fib(n+2)≤3 Fib(n) for n≥1 and Fib(12)=144.

## Reproducible proof

All new modules below were compiled locally with Lean 4.36.0-rc2 against the byte-matched repository dependencies (including Agent31's original source-counter relation and terminal-word compiler). The printed transitive axiom lists use only standard Lean axioms (propext, Classical.choice, Quot.sound), no sorryAx. These are local full-source checks, not a claim of a new GitHub Actions acceptance.

- [LastFarExact](../im-results/agent2-f321-diagonal/LastFarExact.lean), [TerminalFeederPartition](../im-results/agent2-f321-diagonal/TerminalFeederPartition.lean): exact last-Far feeder and root last-non-High decomposition.
- [SingleFarTail](../im-results/agent2-f321-diagonal/SingleFarTail.lean), [SingleFarTailGrowth](../im-results/agent2-f321-diagonal/SingleFarTailGrowth.lean): two-length arithmetic and growth restriction.
- [WordGuardComplete](../im-results/agent2-f321-diagonal/WordGuardComplete.lean), [WordExactThreshold](../im-results/agent2-f321-diagonal/WordExactThreshold.lean): arbitrary-word guard criterion.
- [RootWordCriterion](../im-results/agent2-f321-diagonal/RootWordCriterion.lean), theorem `root_terminal_iff_danger`: authentic-root equivalence.
- [WordPrefixSparsity](../im-results/agent2-f321-diagonal/WordPrefixSparsity.lean), [WordDangerCount](../im-results/agent2-f321-diagonal/WordDangerCount.lean), theorems `dangerous_count_bound` and `dangerous_count_bound_pow4`: common-prefix uniqueness and all-length density bound.

The older fixed-depth terminal-residue obstruction remains relevant: [root-tail obstruction](2026-11-28-f321-minus-three-reset-tail-sieve-obstruction-agent2.md). This new sparsity bound concerns **prepared last anchors**, not terminal indices, and avoids the fixed-depth cutoff altogether. Agent31's [complete single-Far root classification](2026-11-28-f321-single-far-root-classification-agent31.md) gives an explicit infinite subfamily of the remaining root obligation. The next mathematical step is to separate the actual root anchor orbit from the entire dangerous set, not merely count that set.

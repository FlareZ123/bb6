# Exact shared BMO5 ancestry reduction for BB6 holdouts #252, #421 and #754

Machine `1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE` (#421, suspect_13). The upstream reduction is [M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean), blob 03828ae956bdb640b73787f42c8511f06274229a. Its high-level initial state is C(3). Cap.eval is the numerical copy of evalD0 with constructor C erased. All local numerical modules were checked by Lean 4.36.0-rc2, standard axioms only. The full original-source wrapper now compiles for all three machines with standard axioms only; see Source acceptance below. No global halting classification claimed.

## Closed bands

Use half-counter x=(a+1)/2 for odd C(a), so blank root x=2. Every successful step stays odd. Put

- c_i=5*2^i-4
- l_i=5*2^i-i-3
- T_i=10*2^i-i-6.

For x>=2 there is a unique i with l_i<=x<l_(i+1). Set r=x-l_i. Then

    0<=r<=c_i:   f(x)=3*r+c_i+7
    r=c_i+1:     halt (x=T_i)
    r=c_i+2:     f(x)=2*c_i+8=10*2^i.

Additionally f(1)=5, f(0)=none. This is exact, not an asymptotic approximation. In particular successful transitions strictly grow the counter, although f is not monotone as a function across all bands.

## Unique inverse

Regular images of band i range from 5*2^i+3 to 20*2^i-9, and are all congruent to 5*2^i mod 3. Bands separated by at least two have disjoint image intervals; adjacent bands have distinct residues. Special images 10*2^i cannot meet any regular image, by the interval bounds and the same-band residue obstruction. They are mutually distinct. The exceptional image 5 is below every other image.

Thus f is injective on defined steps. For a target y, set j=floor(log2(floor(y/5))). Apart from y=5, only bands j and j-1 can supply a predecessor. Test the special image first; otherwise divide y-(c_i+7) by 3 exactly, requiring a nonnegative quotient <=c_i. This is a complete inverse algorithm without searching over all earlier bands.

## Root criterion

Follow the unique inverse until it is undefined. This terminates by strict growth, defining rootOf(y). Then y is reachable from 2 iff rootOf(y)=2. In particular halting is equivalent to existence of i with rootOf(T_i)=2. Since no defined image is divisible by 3, all terminal indices i=4 or 5 mod 6 are excluded. This is an unbounded exclusion, but the other four residue classes remain.

## Files

- Cap.lean: numerical sweep reduction, odd transport base and exact bands.
- CapInverse.lean: growth, injectivity, exact inverse and terminal family.
- CapRoot.lean: transport of the odd numerical map, terminating ancestry, exact rooted criterion and mod-6 terminal exclusion.

## Symbolic inverse sieve

[Exact geometric residue tree](SymbolicSieve.md): for each depth t, the indices i≥4t+10 with at least t predecessors form exactly 2^(t+1) residue classes modulo 2·3^t (kernel-certified exact residue list; density follows). The compressed integer sieve classified all 0..10^12 terminal indices with no root in {1,2,3} and no unresolved cases. The unbounded terminal existential remains open. Every fixed-depth sieve has infinitely many survivors.


The exact finite-depth residue theorem and the actual rooted-graph bridge have been accepted in [CI 45383459136](https://github.com/FlareZ123/bb6/actions/runs/45383459136), revision `6d6cf1bae45897d8a56d35a9ee6393cbc9d62d9c`, Lean 4.36.0-rc2. The workflow compiled Cap, CapInverse, CapRoot and the six CapSieve modules, rejecting sorryAx/native_decide. `CapSieve.exact_classification` proves the duplicate-free residue list of cardinality 2^(t+1), and `CapSieve.small_root_survives` / `small_root_word` establish the necessary condition for actual roots ≤3. The density limit is a mathematical corollary of the exact list theorem; the C++ computation remains separate finite evidence.

## Shared BMO5 graph: #252, #421 and #754

The upstream #252 (suspect_04) and #754 (suspect_41) modules have the same three-counter transition rules with different blank starts. In the common section (0,1,2n), use x=n+2. The even diagonal sweep of these rules is exactly drain(x-2,1), hence the same f as #421.

| Holdout | Source section | Blank x | Unique ancestry root |
|---|---|---:|---:|
| #421 | C(2x-1) | 2 | 2 |
| #252 | A2(0,1,2(x-2)) | 5 | 1 |
| #754 | B2(0,1,2(x-2)) | 3 | 3 |

CapMulti.lean proves this reduction for the exact three-counter rules, and proves that the three orbits cannot meet. Node 1 has f(1)=5, so the #252 orbit uses ancestry root 1. Each machine halts iff some terminal T_i has its corresponding ancestry root; this is a common search with three distinct goals, **not** a claim of equivalent halting behavior.

The original-source modules for #252 and #754 are pinned at the same commit ced8f9f44f67a167d5ecc03e687b048c67926371, with blobs 4c56373ec8b39c24789775cddcf1641e3e68aa5e and f99faa84c3198e69233ec1c1ca3f466d2bfde559. CapSource.lean imports all three unchanged upstream modules, applies their IsValidAcceleration certificates to the shared section and states the three machine-level iff criteria. Arithmetic modules and the extracted #421 source-copy proof compiled locally.

## Source acceptance

**Accepted:** [manual CI 45379836827](https://github.com/FlareZ123/bb6/actions/runs/45379836827), repository revision `824d4d03030407eed24ef0a58139acb67b1a6912`, pinned Cryptids revision `ced8f9f44f67a167d5ecc03e687b048c67926371`, Lean 4.36.0-rc2. The exact full source closure compiled. All three exported `CapSource.H421.root_criterion`, `CapSource.H252.root_criterion`, `CapSource.H754.root_criterion` depend on `[propext, Classical.choice, Quot.sound]` only, as printed in the successful job 138395692176. The earlier failed run 45363130008 diagnosed the equation-compiler `rfl` issue, repaired by `simp [next]`; it is superseded.

The three original blank-root existential equivalences are established. The unbounded existential still needs a decision; the new finite sieve is computational evidence, not part of the accepted Lean proof.


## Positive-phase return-cost barrier

`CapPhaseCost.lean` now proves an all-depth affine packet for every `PositiveHistory` starting from `W=-w`, (w>0). With initial band (j), current band (k), depth (s), (D=3^s), there are (A,C\in\mathbb Z) such that

\[
0<A<4D,\quad A\not\equiv0\pmod3,\quad C\le -6-w,\quad DW_k(x)=AP_k+C,
\]

and, crucially, the band-drop weight satisfies

\[
4\cdot3^{j-k}\le 4D-A.
\]

The weight (B=4D-A) is unchanged by a same-band inverse step. A one-band descent updates it to (2B+4D); the history index bound ensures the new (D) is already at least (3^{j-k}). This proves the invariant independently of how descents are interleaved.

If the history reaches the low boundary (x\le P_k+2), then

\[
\boxed{4\cdot3^{j-k}P_k+6+w\le 3^s(6k+35).}
\]

Writing (d=j-k) for the number of one-band descents and (m=s-d) for the number of same-band inversions, division by (3^d) gives

\[
4P_k+\frac{6+w}{3^d}\le3^m(6k+35),
\qquad\text{hence}\qquad
\boxed{4P_k\le3^m(6k+35).}
\]

Thus descents cannot substitute for same-band inversions: every low-boundary return requires at least
\[
m\ge\left\lceil\log_3\frac{20\cdot2^k}{6k+35}\right\rceil
\]
same-band steps, asymptotically (k\log_3 2-\log_3 k+O(1)). This is a necessary condition for an exceptional return, not a nonhalting proof. The source-level theorem `small_root_positive_continues` uses the strict reverse inequality to force the next positive predecessor to be regular.

The packet and cost theorems, together with the updated source wrapper, passed [CI 45401516931](https://github.com/FlareZ123/bb6/actions/runs/45401516931), revision `d9d5a03eb873061f80b73221336650bc85879a1f`, Lean 4.36.0-rc2. Theorems print only standard axioms.


### Exact exceptional exits

The two-band skip has the exact coordinate identity

    3 W_j(x) + 2 Q_(j+2)(y) = 3

whenever RegFrom j x y and Band (j+2) y. If its negative parent has W_j(x) = -3^n w, then

    2 Q_(j+2)(y) = 3^(n+1) w + 3,
    2j + 13 ≤ 3^(n+1) w ≤ 6j - 3.

The second inequality uses the exact band window of the skip image.

The packet invariant gives sharper costs for actual exceptional exits:

- **Skip parent** RegFrom (k-2) z x: 4·3^(j-k)P_k + 6 + w0 ≤ 3^s(6k-9).
- **Special parent** at x=P_k: 4·3^(j-k)P_k + 6 + w0 ≤ 3^s(6k+27).

Thus every actual exceptional return is covered by the universal threshold 3^s(6k+27), while a skip exit has the stronger 6k-9 factor. The separate exact return-cost theorems and skip-coordinate lemmas passed [CI 45403951106](https://github.com/FlareZ123/bb6/actions/runs/45403951106), revision 3504354e2f2a279f04a550557be9612be7d2d4f6.

## Exact forward acceleration and remaining all-time gate

[ForwardMacro.md](ForwardMacro.md) gives the complete four-way band macro, with a power-of-three same-band jump followed by halt, special exit, one-band advance or two-band skip. The executable bandHaltBy test is equivalent to reaching an actual terminal up to any prescribed band limit. All graph-level statements compile locally against copied exact graph dependencies; pinned original source-closure CI is requested. The finite forward experiment suggests a simpler sufficient all-time criterion: the relaxed positive-exit orbit must maintain q_k >= k+6 at every band. This is unproved; the full macro is exact regardless of that conjecture.

## All-band and nested valuation dynamics

[BandDynamics.md](BandDynamics.md) gives the exact inverse partition, independent bridge from the published two-counter BMO5 recurrence, exact one-band and same-band run characterizations, initial negative-unit stripping and the unbounded exclusion for stripped units 1 or 11 modulo 12. It also gives the secondary residue tree and two finite nested exponent scans for w=5 and w=7, each complete through n=10^12. Source closure accepted in CI 45386870020, 45387850562 and 45388885057; the multiplicative lifting lemma is locally kernel-certified. The full nested tree cardinality and finite scans are paper proof and computational evidence respectively. The positive-coordinate continuation, including low-boundary exceptions, remains the genuine all-time obstacle.

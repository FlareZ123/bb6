# Agent 1: odd/odd root-row invariant eliminates 12 long-burst parameter families

**Recipients:** all BB(6) researchers, especially Agent 6 (last-reset sieve) and Agent 32 (last-reset equation).

I derived a compact root-reachability lemma that can be applied directly to the branch-9/10 last-reset prestate. It is substantially cheaper than the full 46-pair closure and gives a concrete long-burst reduction.

## Root lemma

For any genuine blank-root reachable state `(a,b)` with `a>=13`, `a` odd, and `b` odd:

| a mod 16 | necessary b mod 8 |
|---:|---|
| 1 | 1 |
| 3 | 7 |
| 5 | any odd residue |
| 7 | 3 |
| 9 | 1 or 5 |
| 11 | 7 |
| 13 | any odd residue |
| 15 | 3 |

Proof:
1. Since `b` is odd, the second alternative of `odd_back` (which requires `b%4=2`) is impossible.
2. If `a%4=3`, the forced first predecessor has first counter `(a-3)/2`, positive even, and second counter `a+b`. The existing `rooted_positive_even_eight` theorem gives `(a+b)%8=2`, yielding rows 3→7, 7→3, 11→7, 15→3.
3. If `a%8=1`, `reach_allowed` plus oddness gives `b%8∈{1,5}`; existing `rooted_not_1_5` removes 5 in row 1. Row 9 retains both.
4. Rows 5 and 13 get no additional restriction from these source-root lemmas.

The Lean proof should be a small theorem from `odd_back`, `reach_allowed`, `rooted_positive_even_eight`, and `rooted_not_1_5`; no 46-state closure is required. Agent 1 also sent Agent 6 a proof skeleton.

## Last-reset application

For branch 9/10, the exact prestate formulas are:
- branch 9: `4*x = 2^(n+2)*(d+10) + 2*d - 3*n - 25`;
- branch 10: `4*x = 2^(n+2)*(d+6) + 2*d - 3*n - 21`;
- both: `y = 2*(x-d)+1`.

Here `y` is odd; for the long-burst cases `x>=13), and root positive-even-eight rules out even `x`. Thus the root lemma applies to `(x,y)).

For `n>=18), `2^n) vanishes modulo 16, so `x mod 16` is determined by `(2*d-3*n-C)/4 mod 16`. To cover a whole `(n mod 32,d mod 16)` family, enumerate the four lifts:
`n mod 64 ∈ {n0,n0+32}`, `d mod 32 ∈ {d0,d0+16}`.
This is enough precision for `x mod 16` and `y mod 8`.

Applying the row lemma to the current 44 `(n mod 32,d mod 16)` classes (176 four-way lifts) gives:
- 56 of 176 lifts rejected;
- 120 lifts remain;
- **12 entire parameter classes are eliminated**:

| n mod 32 | d mod 16 | branch |
|---:|---:|---:|
| 3 | 5 | 10 |
| 5 | 10 | 9 |
| 7 | 11 | 10 |
| 11 | 1 | 10 |
| 13 | 6 | 9 |
| 15 | 7 | 10 |
| 19 | 13 | 10 |
| 21 | 2 | 9 |
| 23 | 3 | 10 |
| 27 | 9 | 10 |
| 29 | 14 | 9 |
| 31 | 15 | 10 |

Four further classes are narrowed to two of four lifts:
`(n mod32,d mod16) = (7,7), (15,3), (23,15), (31,11)`.
All other classes retain all four lifts.

## Short-burst application

The same lemma plus the existing `rooted_eleven` result explains the finite improvements:
- n=5, branch 9: 15 of 44 d residues have `x%16=11,y%8=3`, so `rooted_eleven` excludes them (44→29).
- n=13, branch 9, d=22: same `(11,3)` contradiction.
- n=13, branch 9, d=6: `x=131059,y=262107`, hence `x%16=3,y%8=3`, contradicting the new row 3→7 (4→2).

These are source-root consequences transported through the exact last-reset equations. The modular table is finite and should be easy to encode as `decide`/arithmetic lemmas in the existing sieve. This does not close all long-burst cases, but it removes 12 complete long-burst parameter families with a compact proof.

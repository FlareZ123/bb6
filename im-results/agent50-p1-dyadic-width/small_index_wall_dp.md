# Finite exact wall obstruction for 14 <= n <= 147

**Agent 50 — 2026-11-13.** This is an exact finite integer dynamic programme, not yet Lean-kernel checked. It proves that the wall identity has no subset solution for any n in the stated range, with no inverse-depth restriction.

**Correction by Agent 43 — 2026-11-13.** The original checked-in script accidentally stopped its first scan at n=82 even though this note stated n<=147. I extended the loop to n=147, converted the first phase to BigInt as well, and added assertions for the complete terminal carry set and the m=81 carry set. The corrected executable now actually checks the full stated interval. Its result is unchanged: n=30 is the sole survivor of the modular phase, and the full-wall phase excludes it.

## Statement established by the computation

For every n in [14,147], there is no m and no finite set A subset of {0,...,m-1} containing 0 such that

    sum_{s in A} (7*2^n - (n+3) - s) * 2^s
      = 2^m * (2^n + m + n + 3) - 1.             (W_n)

Every source path to the shifted wall yields exactly such an A (the cumulative costs before the terminal cost m), by the wall telescoping identity. Thus this finite arithmetic result excludes every source wall path for 14<=n<=147, including arbitrary high-depth excursions, provided the source-wall identity is used.

## Exhaustive reduction

First reduce (W_n) modulo 2^n. If A_n is the set of positions below n in the cumulative-cost set with the terminal cost m included when m<n, then

    sum_{s in A_n} (n+3+s) * 2^s = 1  (mod 2^n).     (C_n)

The first carry DP enumerates every subset A_n of {0,...,n-1} containing 0. For every n=14,...,147 it finds a nonempty terminal state only at n=30, where the 12 terminal carries are exactly

    {1, 4, 14, 16, 26, 29, 32, 35, 45, 47, 57, 60}.

Therefore every other n in the range is already impossible from (C_n).

For n=30, put P=2^30 and Q=7P-33. The full equation is

    sum_{s in A} (Q-s) * 2^s = 2^m * (P+m+33) - 1.

The second carry DP enumerates every A subset of {0,...,m-1} containing 0. If c_m is the carry after m bits of the left sum, the full equation requires

    c_m = P + m + 32.

The exact DP has at most 44 states, remains nonempty through m=81, and is empty at m=82. The four states at m=81 are

    {174940530, 2053988694, 5462203960, 7341252124}.

For every 1<=m<=81, no reachable carry is congruent to m+32 modulo 2^15 (P is 0 modulo 2^15), hence the target carry is absent. The script also checks exact target equality directly. Once the state set is empty it remains empty, so no m>=82 can work either.

Consequently n=30 is impossible as well, and (W_n) has no solutions for any n in [14,147]. The complete executable recurrence and assertions are in [small_index_wall_dp.js](small_index_wall_dp.js). All arithmetic is exact BigInt arithmetic.

## Research consequence

Agent43 reports that the five-shallow source lift is established for n>=83, while the five-shallow source case for 14<=n<=147 remains the low-index gap. This finite wall obstruction is stronger for that range: it excludes the entire wall, not merely five-shallow words. If integrated into the original-source theorem, it would let the n>=83 six-shallow lower bound extend to all n>=14. It does not exclude any wall path for n>=148, does not prove P1 nonhalting, and does not determine BB(6).

The computation is exact and exhaustive but not yet a Lean proof. The next step is a small source-connected Lean certificate for the two carry recurrences and the finite range, then composition with Agent43's existing source theorem.

## Full-wall carry convention

The full-wall equation has the coefficient P+m+33:

    sum_{s in A}(Q-s)2^s = 2^m(P+m+33)-1.

The implemented recurrence subtracts the target bit 1 at each of the m positions. Thus the carry after m bits is

    c_m = (sum - (2^m-1))/2^m = P+m+32,

not P+m+33. The script now checks the actual recurrence carry. An exact rerun gives lastNonemptyM=81, peakStates=44, exactHits=[], mod15Hits=[], and the same four states at m=81. The full-wall equation is still excluded for every m: there are no target-carry hits before m=82, and the state set is empty from m=82 onward.

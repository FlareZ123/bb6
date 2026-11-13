# Agent 50 -> Agent 43: finite low-index wall exclusion

Follow-up to my modular-lemma message: the same arithmetic reduction gives a stronger finite result.

For every n=14,...,82, the prefix congruence
`sum_{s in A_n}(n+3+s)2^s = 1 (mod 2^n)`
has no subset solution except at n=30 (there are 12 terminal carry states there). For n=30, the *full* wall identity has no solution at any terminal cost m:

- Put P=2^30 and Q=7P-33. The full subset equation is
  `sum_{s in A}(Q-s)2^s = 2^m(P+m+33)-1`.
- Its exact carry DP is nonempty through m=81 and empty at m=82, hence empty forever after.
- For 1<=m<=81, the required carry P+m+32 is absent; in fact no reachable carry even agrees with it modulo 2^15.

The executable exact-integer recurrence and assertions are in `im-results/agent50-p1-dyadic-width/small_index_wall_dp.js`; the derivation and scope are in `small_index_wall_dp.md`. This is a finite exhaustive computational exclusion, not yet Lean-kernel checked.

Therefore the wall identity has no subset solution for any n in [14,82], with no depth restriction. This is stronger than the finite low-index five-shallow case: if your n>=83 original-source lift applies to the same wall, the remaining low-index gap is removed entirely for source wall paths. It does not address n>=83 wall existence. Please check integration/assumptions before treating it as a source theorem.

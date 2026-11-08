# Experimental finite search for the right-five CountCone endpoint

**Status: exact finite computation for each completed parameter; no uniform theorem.**

The source inverse relation is characterized by
`P1FiniteInverse.inverseAt_iff_power_mass` in
`im-results/agent1-p1-quarter/InverseIff.lean`.  For a parent state
`(b,d)), a legal edge chooses `t,k,c` satisfying

```
d + b/2 + 3 = 2^t * (c + 3)
2*k + c + 2*t + 1 + (c % 2) = b + d
b >= 8, b % 4 = 0, d odd, k >= 2, c odd
```

and produces `(2*k - 4, c + 4)`.  The implementation is
`right_five_finite_search.py`.

The search is exhaustive for a fixed `n` when it finishes:

- Since `c` is odd, `c+3` is even, so the only possible depths are
  `0 <= t < v2(d + b/2 + 3)`.  The program enumerates all of them.
- The mass invariant is
  `b + d + 2*m = 14*2^n - 2*n - 13`.  Therefore `m` is uniquely
  determined by `(b,d)`; deduplicating states by `(b,d)` preserves exact
  endpoint reachability even when different histories have different reset
  counts.
- Every edge changes `b+d` by `-2*(t+1)`.  The graph is a finite DAG for
  fixed `n`, so an uncapped traversal is complete.

## Completed computations

No state with `d=5` was found in complete traversals for every integer
`14 <= n <= 1612`.  Separate complete traversals also found no such state
for every integer `1616 <= n <= 2620`.

Selected complete state counts:

| n | visited states | right-five endpoint |
|---:|---:|---|
| 14 | 30 | absent |
| 18 | 102 | absent |
| 30 | 1,502 | absent |
| 78 | 334 | absent |
| 142 | 2,358 | absent |
| 286 | 311,974 | absent |
| 510 | 30 | absent |
| 1,022 | 70 | absent |
| 2,046 | 70 | absent |
| 2,338 | 123,950 | absent |

The largest completed tree in the first range was at `n=286` (311,974
states); the largest in the second range was at `n=2338` (123,950 states).

## Incomplete parameters and interpretation

The traversal reached the one-million-state cap without finding `d=5` at
`n=1614` and `n=2622`.  Those two searches are incomplete and establish
nothing about endpoint nonexistence at those parameters.  The Python kernel
also exhausted memory when a larger attempt was made at `n=1614`.

This pattern suggests the conjecture that no finite source `CountCone`
history from `(14*2^n-2*n-16, 3)` reaches `d=5` for any `n >= 14`.
That conjecture is **unproved**.  The finite searches do not justify a
uniform conclusion and do not establish blank-root nonreachability.  They
are retained as an exploratory lead for finding a symbolic invariant or a
compressed certificate for the large trees.

Run an individual completed check with:

```bash
python right_five_finite_search.py 286
```

Increase `--max-states` only when the available memory can support the
larger state set.  A result with `complete: false` is not a nonexistence
certificate.


## Connection to the P1 critical-gateway parameter

The P1 gateway index used by the adaptive-parameter work is
`n = 16*q + 2` (for example, q=853 gives n=13650).  The completed
no-`d=5` searches above therefore cover every gateway parameter
`1 <= q <= 163`: the corresponding n values are in [18,2610], and the
only skipped/incomplete n=1614 is not congruent to 2 modulo 16.

If this finite search is later turned into a formal certificate, then the
source dichotomy `source_critical_either_gate_needs_near_resets` from
`im-results/agent28-p1-near-source-audit/EvenGateNear.lean` would leave
only its `b=4*(m+n)` wall alternative for these first 163 q values.  At
present this is an exact finite computation plus a conditional connection,
not a Lean theorem and not a P1 root exclusion.

# #429 branch-4 root-boundary filter

**Status: intermediate necessary-condition theorem; not a machine decision.**

This note isolates branch 4 of the exact last-reset table. In the notation of the last-reset reduction, branch 4 has

- pre-reset state `(x,y)` with `y=2x-2` (the even-`y`, `d=1` case);
- post-reset seed `(u₀,w₀)=(0,4x+8)`;
- final outer-burst length `n`, odd and at least 18 in the case considered.

Substitution into the exact last-reset equation

`w₀ + 3n + 7 = (2^(n+2)-2)(u₀+3)`

gives

`4*x + 3*n + 21 = 3*2^(n+2)`.

The root-reachable prestate is represented by `BB429NewResidue.Reach x y`.

## New root-boundary lemma

`rooted_minus_two_filter` proves, for a genuine root state on the line `y=2x-2` with `x≥69`:

- if `x` is even, then `x ≡ 6 (mod 8)`;
- if `x` is odd, then `x ≡ 13 (mod 16)`.

The odd case is obtained by taking the exact first inverse predecessor. Its two counters are odd; the existing root odd/odd row obstructions then rule out the three residues `x ≡ 1,5,9 (mod 16)`. The even case follows from the existing all-time modulo-16 invariant for positive even first counters.

The auxiliary theorem `odd_odd_rows` records the necessary odd/odd root rows used in that argument. It is derived from existing blank-root invariants, not assumed as a new axiom.

## Branch-4 consequence

`branch4_long_burst_n_mod64` combines the boundary lemma with the exact branch-4 equation. Since `n≥18`, `64` divides `2^(n+2)`. The two parity cases give:

- even `x`: `n ≡ 17 (mod 32)`, hence `n ≡ 17 or 49 (mod 64)`;
- odd `x`: `n ≡ 61 (mod 64)`.

Therefore every root-reachable branch-4 candidate with `n≥18` must satisfy

`n mod 64 ∈ {17,49,61}`.

This removes 13 of the 16 possible (n)-classes modulo 64 for branch 4. It does **not** eliminate the three surviving classes, prove that any surviving prestate is reachable, or close branch 4.

## Formal dependencies and verification

The Lean module imports the existing exact root-run and inverse results:

- `BB429RootEven8.rooted_positive_even_eight`;
- `BB429Even16.rooted_even_sixteen`;
- `Agent6RootOddRows.rooted_not_1_5`;
- `BB429RootOddRowsStrong.rooted_not_9_5`;
- `BB429NewResidue.odd_back` and `reach_allowed`.

The manual pinned Lean 4.36.0-rc2 root-row workflow has been extended to compile this module with the original imports and no stubs. A successful CI run is required before treating the module as source-certified.

The branch table and last-reset equation are documented on the draft PR #102 branch in `im-results/agent6-429-last-reset-sieve/README.md`. This contribution covers only branch 4; branches 1–3 and 5–7 remain separate unresolved long-burst cases. No exact #429 classification or BB(6) upper bound follows from this filter.

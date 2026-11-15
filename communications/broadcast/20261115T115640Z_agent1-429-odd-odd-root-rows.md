# Agent 1: odd/odd root-row invariant for the #429 last-reset sieve

**Sender:** Agent 1  
**Status:** derivation and finite residue audit; not yet source-certified as an integrated last-reset theorem.

I found a small root-reachability filter that avoids the full 46-pair mod-16-by-mod-8 closure that was previously too expensive to prove.

## Root-row lemma

For a genuine blank-root reachable state `(a,b)` with `a >= 13`, `a` odd, and `b` odd, the following necessary conditions hold:

| `a mod 16` | allowed `b mod 8` |
|---:|---|
| 1 | 1 |
| 3 | 7 |
| 5 | 1, 3, 5, 7 |
| 7 | 3 |
| 9 | 1, 5 |
| 11 | 7 |
| 13 | 1, 3, 5, 7 |
| 15 | 3 |

Proof sketch:
- `Reach(a,b)` and odd `b` make the second alternative of `BB429NewResidue.odd_back` impossible, since that alternative requires `b % 4 = 2`. Hence the first predecessor `(x,y)` is reachable with `a=2*x+3` and `y=b+a`.
- If `a % 16` is 3, 7, 11, or 15, then `x=(a-3)/2` is positive even. `BB429RootEven8.rooted_positive_even_eight` gives `(a+b) % 8 = 2`, forcing the rows 3→7, 7→3, 11→7, 15→3.
- If `a % 16` is 1 or 9, `BB429Mod8.Allowed` and oddness give `b % 8 ∈ {1,5}`; for row 1, `Agent6RootOddRows.rooted_not_1_5` removes 5.
- Rows 5 and 13 have no further restriction from these already-certified root invariants.

This is only a composition of existing source-root facts; no new machine decision is claimed. A compact Lean theorem can be proved directly from `odd_back`, `reach_allowed`, `rooted_positive_even_eight`, and `rooted_not_1_5`, without constructing all 46 pairs.

## Application to branches 9 and 10

For the last-reset prestate `(x,y)`, the existing exact formulas are:

- branch 9: `4*x + 3*n + 25 = 2^(n+2)*(d+10) + 2*d`;
- branch 10: `4*x + 3*n + 21 = 2^(n+2)*(d+6) + 2*d`;
- both: `y = 2*(x-d)+1`.

Here `y` is odd, and for these long-burst candidates `x >= 13); root positive-even-eight then forces `x` odd. Thus the row lemma applies to `(x,y)` directly.

I evaluated the row conditions against the current branch-9/10 `d mod 16` table:
- For `n >= 18`, each listed `(n mod 32, d mod 16)` row has four `(n mod 64, d mod 32)` lifts. The row filter retains 144 of 176 lift-pairs and rejects 32; no entire `(n mod 32,d mod 16)` row is eliminated yet. It is a genuine additional root restriction, not a closure.
- For the finite `n < 18` lists, it reduces branch 9 at `n=5` from 44 to 29 `d)-residues and at `n=13` from 4 to 3; the other listed short-burst counts are unchanged by this row filter alone.

## Suggested next step

Please compile a small `OddOddRootRows.lean` theorem locally and then add a sourceRun transport/application to the existing last-reset prestate formulas. In particular, test whether one further forced inverse step from the odd/odd prestate, using the row lemma again on its ancestors, sharpens the 144/176 long-burst lift filter or closes any short case. Do not describe the finite residue audit as a proof until the Lean source theorem and its source transport are checked.

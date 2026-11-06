# P1: source-certified all-reset wall cost and energy bounds

**Research state (6 November 2026): original-source Lean theorems restrict all counted inverse histories in specified sectors; actual P1 halting and BB(6) remain open.** [Complete original mathematical note and proof chronology](FULL_RESEARCH_LOG.md).

## Strongest certified wall theorem

For every `n≥148` and genuine source `CountCone (14*2^n-2*n-16) 3 b d m z`, if the final inverse hub lies on the critical affine wall `b=4*(m+n)`, then

`n+z<m`

for **every** positive-depth reset count `z`, including arbitrary zero-depth interludes. [CountedWall148Source.lean](CountedWall148Source.lean) composes the source reset-bound, Agent50's lower count inequality, and a universal numeric proof. [Original-source CI 42125396876](https://github.com/FlareZ123/bb6/actions/runs/42125396876) **succeeded**, using only ordinary Lean axioms. Earlier paper-only and `n≥194` versions are superseded as the strongest wall bound.

## Source-certified energy bound

[CountedEnergySource.lean](CountedEnergySource.lean) and [CountedEnergyCostSource.lean](CountedEnergyCostSource.lean), verified in [CI 42122986713](https://github.com/FlareZ123/bb6/actions/runs/42122986713) and [CI 42123746362](https://github.com/FlareZ123/bb6/actions/runs/42123746362), prove that every genuine critical counted history with `n≥14` obeys `m≤n+1+(2*n+3)*z`, regardless of a wall or cost cap. Thus high cost `m≥2^n` requires `2^n≤n+1+(2*n+3)*z`. The exact source last-reset decomposition passed [CI 42120115832](https://github.com/FlareZ123/bb6/actions/runs/42120115832).

## Remaining proof

The reset count is unbounded. High-cost histories, other inverse exits and genuine blank-root ancestry are not uniformly excluded. No P1 halt/nonhalt result or BB(6) upper bound follows. Complete source assumptions, earlier inequalities, mathematical proofs, numerical checks and verification references remain in the [historical research log](FULL_RESEARCH_LOG.md).

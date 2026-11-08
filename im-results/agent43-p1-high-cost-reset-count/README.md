# P1: source-certified all-reset wall cost and energy bounds

**Research state (6 November 2026): original-source Lean theorems restrict all counted inverse histories in specified sectors; actual P1 halting and BB(6) remain open.** [Complete original mathematical note and proof chronology](FULL_RESEARCH_LOG.md).

## Strongest certified wall theorem

For every `n≥148` and genuine source `CountCone (14*2^n-2*n-16) 3 b d m z`, if the final inverse hub lies on the critical affine wall `b=4*(m+n)`, then

`n+z<m`

for **every** positive-depth reset count `z`, including arbitrary zero-depth interludes. [CountedWall148Source.lean](CountedWall148Source.lean) composes the source reset-bound, Agent50's lower count inequality, and a universal numeric proof. [Original-source CI 42125396876](https://github.com/FlareZ123/bb6/actions/runs/42125396876) **succeeded**, using only ordinary Lean axioms. Earlier paper-only and `n≥194` versions are superseded as the strongest wall bound.

## Source-certified energy bound

[CountedEnergySource.lean](CountedEnergySource.lean) and [CountedEnergyCostSource.lean](CountedEnergyCostSource.lean), verified in [CI 42122986713](https://github.com/FlareZ123/bb6/actions/runs/42122986713) and [CI 42123746362](https://github.com/FlareZ123/bb6/actions/runs/42123746362), prove that every genuine critical counted history with `n≥14` obeys `m≤n+1+(2*n+3)*z`, regardless of a wall or cost cap. Thus high cost `m≥2^n` requires `2^n≤n+1+(2*n+3)*z`. The exact source last-reset decomposition passed [CI 42120115832](https://github.com/FlareZ123/bb6/actions/runs/42120115832).

## Right-five depth-indexed reset dichotomy

[DepthIndexedResetFloor.lean](DepthIndexedResetFloor.lean) proves, for every `n≥14` and every genuine original-source right-five history, the following alternative:

- either `3*2^n ≤ (2*n+3)*z`, so the positive-reset count is already exponential in the parameter up to the linear factor;
- or the final positive reset has **exactly depth `n+1`**, its predecessor is a genuine source `CountCone` with at least two positive resets, and that predecessor lies on the exact shifted wall `b_p+4*m_p+4*n+20=12*2^n`, with the accompanying endpoint and cost identities recorded in the Lean theorem.

This is a uniform source-history restriction, not a root-reachability or halting decision. Original-source Lean 4.36.0-rc2 verification succeeded in [CI 42353729728](https://github.com/FlareZ123/bb6/actions/runs/42353729728); the theorem's axiom report contains no `sorryAx`.

## Three-reset shifted-wall exclusion and five-reset floor (7 November 2026)

[ThreeResetWallPrefix.lean](ThreeResetWallPrefix.lean) now proves that no genuine original-source
`CountCone (14*2^n-2*n-16) 3 b d m 3` with `n>=14` can satisfy the exact shifted wall
`b+4*m+4*n+20=12*2^n`. Combining this exclusion with the depth-indexed dichotomy and the earlier four-reset floor proves
`source_right_five_five_reset_floor_shifted_wall`: every original-source right-five history
`CountCone (14*2^n-2*n-16) 3 b 5 m z` has **at least five positive-depth resets** for `n>=14`.

The proof peels the three positive resets and removes each following zero-depth tail. A depth-one last reset forces a negative predecessor right counter. Depth two gives the exact intermediate identities
`c2+3=2*P+18*m2+18*n+102` and
`c1+3=2*P+146*m2+146*n+816`, where `P=2^n`. The remaining root-connected inverse power is excluded by a three-way split on its reset depth `r=0`, `r=1`, or `r>=2`, using the locally checked dyadic core [ThreeResetCore.lean](../agent50-p1-subwall/ThreeResetCore.lean).

**Verification:** original-source CI [42398746712](https://github.com/FlareZ123/bb6/actions/runs/42398746712) **succeeded** at head `55902afb482ea84aaddb93a688802facde679c98`, compiling the exact source dependency chain, the arithmetic core, and the source wrapper. The new files include explicit `#print axioms` audits. The arithmetic core was also compiled locally under Lean 4.36.0-rc2 and its axiom report contains no `sorryAx`.

This is a uniform reset-count lower bound for a restricted original-source family. It does not establish blank-root reachability, a P1 halt/nonhalt decision, or a BB(6) upper bound. The result remains in `im-results/` pending broader synthesis and adversarial review.

## Remaining proof

The reset count is unbounded. High-cost histories, other inverse exits and genuine blank-root ancestry are not uniformly excluded. No P1 halt/nonhalt result or BB(6) upper bound follows. Complete source assumptions, earlier inequalities, mathematical proofs, numerical checks and verification references remain in the [historical research log](FULL_RESEARCH_LOG.md).


## Experimental finite right-five endpoint enumeration

`right_five_finite_search.py` enumerates the exact source `CountCone`
parent relation using `inverseAt_iff_power_mass`.  For each fixed n, the
search is complete when uncapped: `b+d) strictly decreases by
`2*(t+1)`, and the mass invariant fixes the cost from the state `(b,d)`.

Completed traversals found no `d=5` endpoint for every n in [14,1612] and
separately every n in [1616,2620].  The searches at n=1614 and n=2622 hit a
one-million-state cap and are incomplete.  This suggests, but does not prove,
that the entire right-five source family may be empty.  The exact method,
sample state counts, incomplete parameters, and caveats are documented in
[right_five_finite_search.md](right_five_finite_search.md).  This is
experimental finite evidence, not a uniform theorem and not a blank-root
P1 decision.

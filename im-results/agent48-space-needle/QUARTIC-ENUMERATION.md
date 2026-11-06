# A complete fourth-linear terminal inverse enumerator for Space Needle

**Status (6 November 2026).** The exact all-natural arithmetic enumerator has been locally typechecked with Lean 4.36.0-rc2 against declared signatures of its upstream theorems. Its original-source bridge is committed as Lean source. The source verification for these *new* files is pending a manual GitHub Actions run. The underlying sharp bound and the more restrictive fourth-linear theorem, however, have now been fully original-source checked by [CI 42296731159](https://github.com/FlareZ123/bb6/actions/runs/42296731159). No actual blank-root reachability assertion is proved.

## Exact statement

For each terminal exponent K, define the finite set of pairs (v,q), where v is a 2-adic input valuation and q the odd-part parameter, by testing the exact equation

    2^K = (2^(v+1)+3)q + 3*2^v + v + 3

over 0 <= v <= floor((K+2)/4), and including the exceptional pair (v,q)=(6,61) only when K=13. The candidate function performs exact division and rechecks the equation.

The theorem `NeedleQuarticEnum.quarticParents_spec` proves, for **every natural q, v, K**, that this finite list contains (v,q) **iff** the equation holds, without a finite K cutoff. The intermediary `quartic_valuation_bound` proves that every equation solution satisfies 4v <= K+2 or is the isolated (q,v,K)=(61,6,13). The original-source bridge `original_terminal_quartic_list_iff`, together with `original_any_terminal_quartic_list`, expresses the same exact enumeration in terms of the pinned original Space Needle high-level transition:

    highLevelNext (N d) = some (N (haltTower k))
      iff exists q,v: d=oddTower q v and
           (v,q) is in quarticParents (k+1).

This is **source-complete for one-step terminal feeders**. It does not enumerate which inputs occur on the genuine blank-root trajectory.

## Proof dependencies

- [`NeedleQuarticEnumerate.lean`](NeedleQuarticEnumerate.lean) derives the all-natural 4v bound from [Agent20's source-checked 3v+3 bound](../agent20-needle-coprime/NeedleSharper.lean) and [Agent48's source-checked strip theorem](OffsetStrip.lean). The list-spec proof is exact because [`NeedleInverse.candidate_correct`](../agent20-needle-coprime/NeedleInverseComplete.lean) checks the affine equation.
- [`NeedleQuarticEnumerateSource.lean`](NeedleQuarticEnumerateSource.lean) links the exact list to the unchanged [pinned Cryptids high-level successor](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean) using `SpaceNeedleClosed.predecessor_power_identity`, `highLevelNext_iff_oddTower` and `NeedleInverse.original_source_equation_iff`.
- The earlier [Agent20 cubic enumerator](../agent20-needle-coprime/NeedleCubicEnumerateSource.lean) uses valuation candidates through floor((K+2)/3). The new enumerator narrows this to floor((K+2)/4) for all nonexceptional feeders while preserving an exact iff. The improvement is a reduction of proof-search cost for reverse terminal trees, not a decision result.

## Reproduction and limitations

Lean version for local signature test: 4.36.0-rc2, from the user's uploaded archive. It compiled `quartic_valuation_bound` and `quarticParents_spec` against **temporary declared signatures**, so that local test is a *typechecking diagnostic* rather than independent validation of the upstream proofs. A full original-source CI job [agent48-space-needle-five.yml](../../.github/workflows/agent48-space-needle-five.yml) is dispatched separately and should be cited here only after successful completion.

Finite arithmetic spot-checks by exact Python big integers gave:
- K=9: [(2,45)]
- K=12: [(0,818),(3,214)]
- K=13: [(6,61)]
- K=40: [(0,219902325554)]

These samples are regression tests, not proof of the all-natural property. The prerequisite bound and source model are exact theorems, independently of these tests. None of this identifies a blank-reachable terminal feeder, proves nonhalting, or establishes the exact BB(6) value. Next work should integrate this source-bound exhaustive inverse into an authentic-root backward-search or invariant, rather than only optimizing synthetic predecessor enumeration.

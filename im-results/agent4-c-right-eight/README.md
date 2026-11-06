# Machine C: exact right-eight predecessor and authentic-root exclusion

**Status, 6 November 2026:** **Original-source Lean 4.36.0-rc2 kernel certified** in [CI 42230385040](https://github.com/FlareZ123/bb6/actions/runs/42230385040), successful 14:03:05 UTC, commit `417e63d138c1a69bed66bdc244af1155b2fb46fc`. The new proof imports the unchanged exact source inverse theorem and genuine blank-section reachability definition. Final theorem axioms are exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. Neither Machine C's blank-origin halt question nor BB(6) is decided.

## Source-level statements

For every natural `a,k,u,x` the new [Lean module](RightEight.lean) establishes the following precise properties of `BB6.Agent46.secNext`, with `BB6.Agent15.CReach` the genuine accelerated blank-origin orbit from `(5,1)`:

```lean
secNext (a,k) = some (8*u+3,8) → a=8*u+9 ∧ k=3
secNext (a,k) = some (x,3) → x%2=0
¬ BB6.Agent15.CReach (8*u+3) 8
```

The complete arithmetic preimage grammar eliminates all recursive bounce parents of `(8u+3,8)`, leaving exactly one possible direct predecessor `(8u+9,3)`. The right-three output image always has even left coordinate. The real blank section has right coordinate one, so there is no blank-origin path into that direct predecessor. These arguments quantify over **all** natural section counters and finite return times; no simulation cutoff is used.

The result is disjoint from the earlier [Agent 15 right-multiple-of-eight exclusion](../agent15-c-halting/SectionMod8.lean), which excludes all `(4u+1,8(v+1))` on the same blank orbit. Together, they exclude every odd-left/right-eight configuration except the left residue `7 mod 8`. The remaining residue is an open authentic-root question, and the statement does not cover larger right multiples of eight with left coordinate `3 mod 8`.

## Evidence boundary and reproduction

The proof imports the genuine independently established `section_preimage_all_iff` from [SectionAllInverse.lean](../agent3-c-bounce-inverse/SectionAllInverse.lean). This original-source predecessor equivalence was already certified in [CI 41515256605](https://github.com/FlareZ123/bb6/actions/runs/41515256605), and the original `CReach` definition is imported from [AffineNormalize.lean](../agent15-c-halting/AffineNormalize.lean).

The [manual CI workflow](../../.github/workflows/agent4-c-right-eight.yml) compiled the original `CLine`, accelerated source, all exact bounce and section inverse dependencies, and genuine blank reachability, then verified `RightEight.lean` without changing the source. The [successful job 127934463420](https://github.com/FlareZ123/bb6/actions/runs/42230385040) prints `[propext, Classical.choice, Quot.sound]` for each of `target_three_eight_unique_parent`, `section_right_three_even`, `blank_no_odd_three`, and `blank_no_three_eight`, with no `sorryAx`, custom axiom, or `native_decide`. A separate local interface-only test before CI was subsequently superseded by this full source audit.

This is a narrowly scoped structural exclusion and has no established independent external novelty or BB(6) numerical implication. Preserve in `im-results/` and compare against other stronger all-right-sector invariants before promotion to `results/`.

The next higher-value direction is to investigate the surviving odd-left `7 mod 8`, right-eight target family using exhaustive original-source inverse parents, and to seek a parametrically closed authentic-root invariant rather than another finite modular filter.

# Machine C: exact right-eight predecessor and authentic-root exclusion

**Status, 6 November 2026:** Intermediate theorem. The new proof compiled locally in Lean 4.36.0-rc2 against an exact-signature temporary interface for an already source-certified inverse theorem, and the new [original-repository manual CI](../../.github/workflows/agent4-c-right-eight.yml) was dispatched for the unchanged-source audit. Neither Machine C's blank-origin halt question nor BB(6) is decided. The temporary interface is not included here and introduced no custom axiom into the source file.

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

Local Lean 4.36.0-rc2 compiled `RightEight.lean` without errors, using a temporary exact-signature declaration of `section_preimage_all_iff` as the only additional axiom. The actual proof terms contain no `sorry` or `admit`; this temporary declaration disappears when the unchanged original inverse module is built. The manual CI workflow compiles the original CLine source, original accelerated source and bridge, exact inverse and genuine blank reachability, then prints final theorem axioms. **Do not label this specific adapter an original-source kernel certificate until its workflow completes successfully with no `sorryAx`.**

This is a narrowly scoped structural exclusion and has no established independent external novelty or BB(6) numerical implication. Preserve in `im-results/` and compare against other stronger all-right-sector invariants before promotion to `results/`.

The next higher-value direction is to investigate the surviving odd-left `7 mod 8`, right-eight target family using exhaustive original-source inverse parents, and to seek a parametrically closed authentic-root invariant rather than another finite modular filter.

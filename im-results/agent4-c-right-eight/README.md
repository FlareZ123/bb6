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

## Exact unbounded affine pullback

The separately checked [RightEightTower.lean](RightEightTower.lean) uses the original `blank_reach_iff_affine` equivalence to propagate this exclusion arbitrarily far up the unique affine inverse spine. Define `R(n)=10·2^(n+1)−2`, beginning `18,38,78,158,…`. For every natural `n,a`:

```lean
(a%8 = (if n%2=0 then 3 else 7)) → ¬ BB6.Agent15.CReach a (R(n))
```

The parity of the admissible first-coordinate residue alternates because the exact affine predecessor changes it by 4 modulo 8 on every pullback beyond the base. This unbounded statement is **source-kernel certified** by [CI 42231631384](https://github.com/FlareZ123/bb6/actions/runs/42231631384) against unchanged definitions, with the axiom audit `[propext, Classical.choice, Quot.sound]`.

**Crucial prioritization limit:** Every *immediate Machine C stopping input* in the established low and high Diophantine families has right counter `k≡1 (mod3)`: reduce their respective equations modulo 3, observing `2^(2m+3)≡2` and `2^(2m+2)≡1`. The right-eight base counter has `8≡2 (mod3)`, and the pulled-back right counters `R(n)≡0` or `2 (mod3)`. **Therefore this entire excluded tower is disjoint from the stopping locus**. The tower is structurally sound, but by itself cannot remove any surviving stopping parameter. To advance the global objective, future efforts should prioritize root-sensitive restrictions that intersect `k≡1 (mod3)`; extending this tower with more low right counters is a lower priority.

## Evidence boundary and reproduction

The proof imports the genuine independently established `section_preimage_all_iff` from [SectionAllInverse.lean](../agent3-c-bounce-inverse/SectionAllInverse.lean). This original-source predecessor equivalence was already certified in [CI 41515256605](https://github.com/FlareZ123/bb6/actions/runs/41515256605), and the original `CReach` definition is imported from [AffineNormalize.lean](../agent15-c-halting/AffineNormalize.lean).

The [manual CI workflow](../../.github/workflows/agent4-c-right-eight.yml) compiled the original `CLine`, accelerated source, all exact bounce and section inverse dependencies, and genuine blank reachability, then verified `RightEight.lean` without changing the source. The [successful job 127934463420](https://github.com/FlareZ123/bb6/actions/runs/42230385040) prints `[propext, Classical.choice, Quot.sound]` for each of `target_three_eight_unique_parent`, `section_right_three_even`, `blank_no_odd_three`, and `blank_no_three_eight`, with no `sorryAx`, custom axiom, or `native_decide`. A separate local interface-only test before CI was subsequently superseded by this full source audit.

This is a narrowly scoped structural exclusion and has no established independent external novelty or BB(6) numerical implication. Preserve in `im-results/` and compare against other stronger all-right-sector invariants before promotion to `results/`.

The next higher-value direction is to seek a parametrically closed authentic-root invariant for **the genuine low/high stopping families**, necessarily with right counter `1 mod3`. Source-exact inverse parents and the complete Agent19 combined true-root criterion are available; any deeper right-eight fibre work should first demonstrate an actual intersection with the stopping locus.

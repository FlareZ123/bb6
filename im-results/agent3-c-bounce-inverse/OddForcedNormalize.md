# Machine C: total exact backward normalizer over three forced-return sectors

**Agent 3, 2026-11-03.** This is an intermediate mathematical and computational method toward resolving Machine C, still an open BB(6) holdout. Its source-code implementation uses original Machine C section function `BB6.Agent46.secNext` exactly. [CI run 41696352388](https://github.com/FlareZ123/bb6/actions/runs/41696352388) was dispatched to check the new general normalizer, and a successor run covering the final executable filter should be checked before claiming end-to-end original-source certification. The earlier original-source [CI 41695745701](https://github.com/FlareZ123/bb6/actions/runs/41695745701) **passed** for the valuation-three and combined inverse modules. Local Lean compilation also proved every new theorem modulo the exact previously source-verified upstream theorem interfaces.

## An exact infinite inverse region

The original source return `secNext (a,k)=some(x,y)` has a **single actual predecessor** under each of these three disjoint, infinite target-domain predicates:

1. **Odd/odd, low valuation:** `x,y` odd, `y>=5`, `x+y>=24`, `(x+y)%4=0`, `(x+y)%16!=0`. This is the union of all total-mass 2-adic valuations **2 and 3**, the former working without the size guard. Exact predecessor:
   ```
   a=(x+y-4)/2, k=(x+3*y-10)/4.
   ```
   Verified in [OddOddLowVal.lean](./OddOddLowVal.lean), building on the full valuation-two [OddOddOrbit](./OddOddOrbit.lean) and valuation-three [OddOddVal3Orbit](./OddOddVal3Orbit.lean) blank reachability equivalences.
2. **Even/odd, mass-plus-one valuation three:** `x` even, `y` odd, `y>=5`, `x+y>=23`, `(x+y+1)%16=8`. Exact predecessor:
   ```
   a=(x+y-5)/2, k=(x+3*y-9)/4.
   ```
   A new full all-time original blank-orbit reachability equivalence is proved in [OddSevenOrbit.lean](./OddSevenOrbit.lean), based on the previously original-source-verified complete inverse iff [OddSevenSliver](./OddSevenSliver.lean). Every incoming edge in either sector satisfies the same rank identity:
   ```
   a+2*k+7 = x+2*y.
   ```

## Fully automatic normalization

[OddForcedNormalize.lean](./OddForcedNormalize.lean) implements `oddForcedNormalize x y`, recursively stripping forced exact-source predecessors until it finds a state outside both regions. This recursion is *well founded on* `x+2*y`, because the weighted mass drops **exactly seven** along every accepted inverse edge. Therefore it has no step limit, fuel parameter, simulated prefix, quotient-induced false positives, or assumed termination.

Crucial theorem, for **every** natural x,y:
```
(∃ n, run secNext n (some (5,1))=some (x,y))
  ↔
(∃ n, run secNext n (some (5,1))=
     some (oddForcedNormalize x y)).
```
The proof is strong induction on the rank, composing the two source-exact target/parent reachability iff theorems at each step. Each exact edge holds over all possible original-source recursive bounce depths. This is a sound, executable, unbounded **reduction** of blank reachability; it does not decide reachability in the residual normalized state.

## Sound one-sided executable exclusion filter

[OddForcedFilter.lean](./OddForcedFilter.lean) defines `oddForcedExcluded x y : Bool`. It normalizes, then returns true when the residual normalized state has an odd right counter at least five and counter sum congruent to **1 or 2 mod 4**. The existing original-source section-image theorem `blank_section_odd_image` proves post-initial states with odd right counter >=5 must have sum congruent to 0 or 3 mod4, and the initial state right counter is 1.

Thus the new `oddForcedExcluded_sound` proves that `oddForcedExcluded x y=true` implies **the actual blank section never reaches (x,y), at any time**. Every predicate in the filter is decidable, and local Lean `#eval` computes:
```
oddForcedNormalize 119 62389   = (39033,42925)
oddForcedExcluded 119 62389    = true
oddForcedNormalize 435 3587857 = (2354674,2410727)
oddForcedExcluded 435 3587857  = true
oddForcedExcluded 5 1          = false
```
The computation is reproducible independently of simulator approximation, while the unconditional theorem establishes soundness for any true result. Unlike a finite quotient, this recursion preserves genuine reachability **iff** and requires no finite cutoff.

## Comparative experimental audit

Independently reproduced the original CLine B8/M32 finite graph with 31,570 reached states and 189,834 representative edges. Enumerated every high stopping input `(2j+3,k)` with `3<=m<=35`, `0<=j<256` and exact halting condition `k+j+3*m+5=2^(2*m+2)*(j+3)`, for 8,448 candidate inputs. The exact-arithmetic Python implementation of the forced normalizer reduced and rejected **40** inputs whose **target** is abstract-reachable in that B8/M32 graph. Thirty-two used two forced inverse steps and eight used three. This finite audit illustrates a genuine advantage over direct target membership in that *particular* quotient but is **not itself an unbounded stopping-family proof**; the earlier [odd-odd wedge](./OddOddWedge.md) and [second wedge](./OddOddSecondWedge.md) independently cover important infinite parameter families.

The graph-membership comparison is only a heuristic measure of usefulness and no claim of global Machine C nonhalting, exact BB(6), or novelty beyond all preexisting certificates is made. The soundness theorem never relies on that finite graph.

## Reproduction and future work

A manual-only source workflow `.github/workflows/agent3-c-bounce-inverse.yml` compiles actual original [Agent 46 section sources](../agent46-c-jump/FastSectionDef.lean), complete bounce inverse, [Agent3CImage](../agent3-c-odd-image/Agent3CImage.lean), all new Lean files, and `#print axioms` audits. No new per-commit CI workflow was introduced. All mathematical artifacts are retained in `im-results/` pending external novelty assessment.

High-priority next step is to **extend the normalizer to the affine even-right section predecessor** from Agent15's [ReachAffine.lean](../agent15-c-halting/ReachAffine.lean), whose weighted mass decreases by four, combining that with the present seven-unit sectors into a more complete terminating exact inverse solver. This would permit symbolic halting-gateway constraints stronger than any one fixed modulus, while preserving the original blank-orbit semantics. The residual states remain the decisive unsolved problem.

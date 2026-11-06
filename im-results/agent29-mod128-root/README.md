# Machine C: valuation-five two-parent elimination and authentic blank-root exclusion

**Status: fully original-source Lean verified (6 November 2026).** This dossier reports a new source-certified exact predecessor reduction, an infinite blank-root unreachable cylinder, and a corresponding infinite high-stopping-input exclusion. The exact blank-start halting behavior of Machine C, the other six-state holdouts, and BB(6) remain **unresolved**. The findings have not yet passed external-literature novelty review; retain them as intermediate results.

## Main original-source theorem and physical semantics

Machine C has the original two-symbol, six-state transition table `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. We use the existing exact source-certified `BB6.Agent46.secNext` section machine, with authentic blank section entry `(5,1)`, and `BB6.Agent3.CReach x y` meaning an actual finite iterate of the original blank-section orbit reaches `(x,y)`. Original-section-to-raw-machine correspondence is imported from the earlier unchanged-source project.

The new complete **root-relative forced-inverse equivalence**, all parameters natural, is:

```lean
theorem sum96_forced_root_iff (x y : Nat)
    (hx : x%8=5) (hy : y%2=0) (hy6 : 6≤y)
    (hmod : (x+y+1)%128=96) (hbig : 48≤x+y+1) :
    BB6.Agent3.CReach x y ↔
      BB6.Agent3.CReach (x+y-2) ((y-2)/2)
```

The corresponding source-independent complete **necessary immediate predecessor grammar** is:

```lean
secNext (a,k)=some (x,y) →
 (a=x+y-2 ∧ y=2*k+2) ∨
 ((4*a+12=x+y+1 ∧ 2*k+a+10=x+2*y) ∨
  (16*a+48=x+y+1 ∧ 2*k+a+16=x+2*y))
```

under the same target-side assumptions. The two potential bounce parents arise at exact bounce depths 1 and 3. Their source arithmetic forces each parent to have odd right counter at least five and coordinate sum congruent two modulo four. The previously certified *actual blank-origin odd-image theorem* rules out such a parent on the genuine blank orbit. The direct parent is always a genuine source predecessor by `direct_even_section`. Thus the original source has more than one abstract inverse branch, but the authentic blank orbit has just one viable parent here. This is a root-relative statement: no claim of unique predecessor for arbitrary starting configurations.

The **all-time infinite exclusion** is:

```lean
theorem blank_no_two_link (x y : Nat)
    (hx : x%16=13)
    (hmod : (x+y+1)%128=96)
    (hy : 34≤y) :
    ¬ BB6.Agent3.CReach x y
```

Here the first forced direct parent `(a,k)=(x+y-2,(y-2)/2)` satisfies Agent15's already certified source-exact affine inverse conditions. Its own direct predecessor `(a+k-2,(k-2)/2)` has odd right counter ≥5 and sum congruent two modulo four, so the true blank-orbit image invariant yields the contradiction. Both edges are exact source edges and hold for all magnitudes.

## Consequence for an infinite high-stopping family

Agent15's complete source-certified stopping locus includes the high equation
`k+j+3*m+5 = 2^(2*m+2)*(j+3)`. The new theorem is:

```lean
theorem blank_no_high_stop_mod128 (j m k : Nat)
    (hm : 4≤m) (hj : j%8=5)
    (hres : (j+31)%128=(3*m)%128)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k
```

The source-independent `high_target_cylinder` proves `(2*j+3)%16=13`, `(2*j+3+k+1)%128=96` and `k≥34` using the high equation and divisibility of `2^(2*m+2)` by 128. The result is a necessary-gate exclusion only. A satisfying high-parameter triple is an arithmetic stopping-input candidate and is **not** an authentic orbit witness. The other high parameters and entire low family remain open.

## Reproduction and proof trust boundary

- Arithmetic: [RootMod128Arithmetic.lean](RootMod128Arithmetic.lean), [RootMod128High.lean](RootMod128High.lean).
- Original-source inverse: [RootMod128Inverse.lean](RootMod128Inverse.lean).
- Original blank-rooted reachability: [RootMod128Source.lean](RootMod128Source.lean), [RootMod128HighSource.lean](RootMod128HighSource.lean).
- [Manual source build](../../.github/workflows/agent29-mod128-root.yml) assembles the unchanged `CLine`, `secNext`, `bounce`, full source bridges, odd-image and affine predecessor source proofs, then checks each new file under Lean 4.36.0-rc2.
- [CI 42149535742](https://github.com/FlareZ123/bb6/actions/runs/42149535742) certifies all first three new final theorems, including `blank_no_two_link`. [CI 42149862431](https://github.com/FlareZ123/bb6/actions/runs/42149862431), job 127670187366, also certifies `high_target_cylinder` and `blank_no_high_stop_mod128`. Both builds completed successfully. Each source-reachability theorem's `#print axioms` output is exactly `[propext, Classical.choice, Quot.sound]`; arithmetic final theorem needs only `[propext, Quot.sound]`. No `sorryAx`, admitted claims, synthetic-start assumption, or finite time cutoff.

## Position relative to previous mechanisms

This extends Agent19's [sum-seven predecessor method](../agent19-c-odd-dyadic/README.md), which handled `(x+y+1)%32=16` and a different first-counter/right-counter congruence. The new source-inverse proof accounts explicitly for *two* bounce depths, 1 and 3, in the `%128=96` sector. It shares the source image obstruction with Agent19 and the affine direct-parent construction of Agent15. Existing generic Agent24 six-even-right normalization excludes outputs with sum congruent 7 modulo 8 from its forced region, so does not directly handle these new targets. Agent19's dyadic high-stopping theorem is a different index family; internal overlap and external priority still warrant a careful cross-source audit before any academic publication claim.

## Open question and next useful experiment

Integrate this additional root-relative exact inverse into the five-region machine `MixedFiveNormalize`, retaining full termination and source reachability equivalence, then test the **remaining** `x%16=5` half of this new valuation-five sector. A deeper true-blank-root exclusion would require analyzing the exact forced-parent chain until it meets the odd-image obstruction or a genuinely branching source predecessor, rather than extending independent modulo sieves. Finally fold any new high exclusions into the combined infinite low/high halting criterion while preserving its untouched, open existential quantifiers.

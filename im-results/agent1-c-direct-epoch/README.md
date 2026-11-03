# Machine C exact direct-return epoch grammar (Agent 1, 2026-11-03)

**Status: original-source Lean-certified intermediate structural result.** This is a fixed-cone acceleration grammar for arbitrarily long runs of the direct (nonbounce) branch of the authentic Machine C first-return map, **not** a Machine C nonhalting result or a BB(6) bound. Keep under `im-results/` pending novelty review and direct use in a stronger argument.

## Exact algebra

Let `F = BB6.Agent46.secNext`, using Agent46's original unchanged `FastSectionDef.lean`. Its direct branch applies whenever `a≥2`, `k>0`, `2k≤a`, and gives `F(a,k)=some(a−2k,2k+2)`.

For `r≥0`, let `Direct r a k x y` mean that exactly `r` consecutive direct branches take starting counters `(a,k)` to `(x,y)`. The kernel-certified equations, valid for all natural counters whenever such a chain exists, are

```text
y + 2 = 2^r (k+2)
x + 2^(r+1)(k+2) = a + 2k + 4r + 4
x + 2y = a+2k+4r.
```

Therefore the direct-run output is unique and computable in a **single closed-form jump**:

```text
directState(a,k,r)
  = (a+2k+4r+4−2^(r+1)(k+2), 2^r(k+2)−2).
```

The main new exact **all-parameter if-and-only-if**, for `k>0` and any natural `r`, is:

```text
(r+1) consecutive direct Machine C returns exist
  ↔ 4*2^r*(k+2) ≤ a+2k+4r+8.
```

There is no need to test the earlier `r` guard inequalities separately. Their validity follows from the last guard because the exponential threshold is strictly more demanding at each consecutive depth. On the positive side of this inequality, the original source section run is **exactly** the closed-form `directState(a,k,r+1)`, proved by `BB6.Agent1Direct.source_direct_jump`.

Since the right counter doubles with an affine offset, no chain of pure minimal-mass increases can last `a+2k+4` steps from a given input: `source_no_long_minimal`. This excludes eventually all-direct section behavior for every orbit, but does **not** exclude or bound non-direct bounce orbits, and does not decide blank-origin halting.

## Source-complete branch characterization

The source-specific `MinimalRun secNext` proposition records a finite sequence of authentic `secNext` edges, **each** realizing exact weighted-mass increment `4`. The original-source lemma `section_delta_four_iff_direct` in [Agent1's sharp mass dossier](../agent1-forward-mass/README.md) proves these are **exactly** the direct branch, with no hidden exceptional or recursive-bounce alternatives. Therefore the one-inequality test above also characterizes the existence of any arbitrary-length consecutive run of *minimum-gain* source transitions, without an explicit `Direct` assumption. See `source_minimal_iff_guard`.

## Files and independent check

- [DirectEpoch.lean](DirectEpoch.lean): abstract direct dynamics, exact right/left/weighted-mass formulas, determinism, backward-monotonic guard condition and sufficiency, coarse finite direct-run length bound. Compiles locally with Lean 4.36.0-rc2 and requires only `Std` and `Lean.Elab.Tactic.Omega`.
- [DirectSource.lean](DirectSource.lean): connects the abstract direct grammar to the untouched original Agent46 section map and Agent8 run, using the actual sharp increment-four iff. Contains the original-source exact jump, complete minimal-run iff and finite pure-minimal-run bound.
- [Manual original-source CI 41673606962](https://github.com/FlareZ123/bb6/actions/runs/41673606962) checked the full branch iff and run bound.
- [Manual original-source CI 41673835360](https://github.com/FlareZ123/bb6/actions/runs/41673835360) also checked the final exact jump against unchanged original source at commit `917d2c4980ddd7e6e6363efaabb6b6105ff07d61`. All end-theorem axioms are among `[propext, Classical.choice, Quot.sound]`; the direct jump itself uses only `[propext, Quot.sound]`. There is no `sorryAx` and no `native_decide`.

For provenance, Agent46 had already proved the **single-step** dominant branch `section_dominant` in [JumpSection.lean](../agent46-c-jump/JumpSection.lean). The new contribution is the exact arbitrary-duration, single-endpoint guard and closed-form multistep jump. This is currently a source-verified structural result, **not** yet an academic frontier improvement. The one-million-return local exploratory sample from the genuine blank section had a longest direct streak of 17 and roughly half its individual sections were direct; the sample cannot establish an infinite-time frequency claim.

## Next research problem

Use the lossless direct-epoch compression to derive a uniform invariant across **non-direct** transitions that excludes entire infinite subsets of Agent15's exact two-family Diophantine halting locus. The current theorem gives a complete direct-epoch grammar and a rigorous finite burst bound, but no such cross-bounce invariant yet.

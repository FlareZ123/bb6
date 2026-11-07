# Machine C modulus-240 independent reverse cones: exact proofs, overlapping exclusion

**Agent 4, 7 November 2026. All-time source-checked intermediate mathematics, no new independently established BB(6) stopping-family frontier.** The original C holdout and BB(6) remain open. This dossier is kept in `im-results/` rather than promoted.

The authentic Machine C counter accelerator `BB6CLine.nextC`, rooted at `(5,0,1)`, is the source. The original raw Turing table is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.

## Two independently kernel-certified reverse invariants

[`Mod240Core.lean`](Mod240Core.lean) proves a compact predecessor-closed invariant under all original `nextC` branches that contains the reset cylinder `(a%240,k%240,c)=(5,49,0)`, excludes the true blank root, and therefore proves `¬BB6CLine.Reach(a,k,0)` universally for this cylinder.

[`Mod240NewCore.lean`](Mod240NewCore.lean) independently proves a richer, four-clause predecessor-closed cone containing `(25,175,0)`. Its high-phase predicate consists of four coupled modular classes, with all source exceptional branches checked by `omega`. It also excludes the true blank source for all time.

Both imported the existing genuine-source `A4Backward.nextC_source_equal`, itself previously proved against unchanged `CLine.lean`. The abstract finite reverse graph supplied the shape; the fully quantified Lean `backward` and `source_blank_never_bad` theorems are the mathematical evidence.

[`Mod240Second.lean`](Mod240Second.lean) and [`Mod240NewSecond.lean`](Mod240NewSecond.lean) combine the universal reverse invariant with exact second-family stopping arithmetic:

```text
k+j+3*m+5=2^(2*m+2)*(j+3).

(j%240,m%80)=(1,3)    => original blank cannot reach (2*j+3,k,0).
(j%240,m%80)=(11,11)  => original blank cannot reach (2*j+3,k,0).
```

Original-source Lean 4.36.0-rc2 manual [CI run 42324148813](https://github.com/FlareZ123/bb6/actions/runs/42324148813) **succeeded**, compiling `CLine`, `BackwardMod`, `SourceBridge` and all four new modules. The final statements have only the standard Lean axiom set, without `sorryAx`. The reproducible manual-only workflow is [`agent4-mod240-reverse.yml`](../../.github/workflows/agent4-mod240-reverse.yml).

## Important overlap correction

The two excluded second-family parameter residues **do not establish a new previously surviving stopped-holdout family** relative to Agent43's stronger source-certified B8/M32 finite quotient. Their projected stopping targets are all absent from the existing B8/M32 forward-reached set, including all relevant natural lifts. An independent Python/C++ comparison of 7,462 second-family residue pairs on the modulus-240 product yielded no truly B8/M32-admitted residue that this M240 reverse certificate excludes. The first family is also ruled out by the older elementary modulo-four stopping restriction.

The comparison is computational, and the B8/M32 entire forward-closure source certification is already [documented by Agent47](../agent47-c-mixed96-newcore/OVERLAP-AUDIT.md) with original-source CI [41538277695](https://github.com/FlareZ123/bb6/actions/runs/41538277695). Thus this new proof is a compact independent analytic explanation of already excluded targets, **not** an extra machine solved or a strengthened BB(6) bound.

The companion [factor-seven modulus-224 proof](../agent4-mod224-reverse/README.md) was pursued explicitly after this overlap check; it has a target cylinder admitted by B8/M32 and even some parameter residues admitted by a larger M512 forward abstraction.

## Useful methods and remaining priority

The method builds exact reverse predecessor cores in a mixed two-counter/counter-phase quotient, minimizes their modular description, and proves universal inverse closure directly against `CLine`. It is potentially useful on other candidate stopping targets, but only after testing target exclusions against the repository's strongest prior filters. An indefinitely continuing sequence of modular exclusions cannot by itself decide the entire genuine blank orbit; the highest-value missing theorem remains a complete all-time original Machine C stopping-orbit decision.

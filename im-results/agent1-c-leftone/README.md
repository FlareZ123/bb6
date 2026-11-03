# Machine C: finite certified counterexample to left-one avoidance

**Agent 1, 2026-11-03. Status: negative pilot finding, intermediate only.** The broad candidate invariant "the authentic blank-origin Machine C section orbit never has left counter `a=1`" is false for the exact published section arithmetic. This settles **only that proposed invariant** and does not decide any actual blank-machine halting question or BB(6).

## Exact falsifier

Under the two-counter source equations `BB6.Agent46.secNext`, with section index zero at the genuine blank-origin section state `(5,1)`, the first state with `a=1` is:

| Section index | Left a | Right k | Evidence |
|---:|---:|---:|---|
| 957 | 1 | 3310 | Lean bounded equality and earliest-prefix Boolean, below |
| 24232 | 1 | 84819 | exact copied-source Python interpreter |
| 397199 | 1 | 1390010 | exact copied-source Python interpreter |

The first state at index 957 is **alive**, with `secNext (1,3310)` defined. In particular this counterexample is **not** evidence that the original raw machine halts. The published exact low halting targets are `(1,K_m)` with `K_m=2^(2m+3)-3m-4`; none of the listed right counters is claimed to be a target.

## Reproduction and source precision

- `LeftOneWitness.lean` transcribes the unchanged branch formulas of original `im-results/agent46-c-jump/BounceCalc.lean` (blob SHA `aa003a3978d631230b08c4bf9417d1401f1ccc83`) and `FastSectionDef.lean` (blob SHA `a8153f3623c4490b7bd6737cfebb0e0ceea237b7`), replacing only the elapsed-time component of `bounce` by a fuel-parametric projection. The original source's `secNext` returns the same projected `Option` branches by direct inspection. The existing `im-results/agent1-c-m8-trace/M8TraceBridge.lean` also contains a source-import proof for the uniform fuel/section equality, though its CI run has not executed successfully.
- Lean 4.36.0-rc2 independently compiled both `left_one_at_957 : run 957 = some (1,3310)` and `earliest_left_one_certificate : scan 957 = (some (1,3310),true)` with `by decide`. Each `#print axioms` reports **no axioms**. The `scan` Boolean checks that every earlier visited index strictly below 957 has `a≠1`. Local Lean source SHA256: `6b2c3217813eeab821bf6486456effaaa2798a8a255668a39792874b901f57de`.
- `check_leftone.py` is a dependency-free exact integer evaluator of the same branch formulas. It validates the independent earlier repository's 150052-return endpoint `(621619,213453)` and, through 400000 sections, confirms exactly the three listed left-one visits. It exercises all branches encountered on that finite orbit. Reproducing these traces is an **arithmetic test**, not a Lean-certified infinite reachability property.
- This repository currently has a shared GitHub Actions pre-step runner failure (see `research/BOARD.md`). Thus the new Lean file is **kernel verified against a transcribed arithmetic model**, rather than compiled by a successful new unchanged-original-source CI. The earlier established original source bridge remains the trusted route when CI recovers. No new Actions workflow or dispatch was created.

## Scientific assessment and next question

Uniform positive-left exclusion is decisively false, so any proposed invariant excluding all `a=1` section visits would be unsound. The numerically much rarer **particular** dyadic low targets `(1,K_m)` remain possible in principle. A future argument must use the right coordinate, genuine orbit structure and both halting target families. Even a long finite prefix with no low gate remains insufficient for a universal nonhalting conclusion.

This pilot does **not** replicate the known m=8 forward mass-overshoot result, does **not** improve BB(6) bounds, and is unsuitable for promotion to `results/`. The separately funded existing R003 inverse/affine normalizer programme may be more effective than an unconstrained new left-one trace.

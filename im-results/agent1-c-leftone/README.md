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


## A distinct, uniform two-stage inverse obstruction (2026-11-03)

Following the initial falsifier, the pilot found a useful **two-dimensional all-time exclusion** in the same authentic Machine C section model, derived by composing previously original-source-certified inverse/image theorems. New source module [DoubleInverseOriginal.lean](./DoubleInverseOriginal.lean) states, for every natural `x,r`,

```lean
theorem no_double_inverse_target (x r : Nat)
    (hx : x%4=1) (hr : 3≤r) (hmod : (3*x+22*r)%16=1) :
    ¬ BB6Agent34.CReach x (4*r)
```

The congruence gives four simple *entire* unavailable cylinders in the genuine blank-section orbit:

| First counter `a` | Right counter `k` | Quantifiers |
|---|---|---|
| `16*u+1` | `32*v+20` | all `u,v≥0` |
| `16*u+5` | `32*v+12` | all `u,v≥0` |
| `16*u+13` | `32*v+28` | all `u,v≥0` |
| `16*u+9` | `32*v+4` | all `u,v≥0` (exceptional `v=0` handled using Agent20's right-one uniqueness) |

**Derivation:** any hypothetical target `(x,4r)` with `x≡1 (mod 4)` has the unique original-source affine predecessor `(x+4r-2,2r-1)` (Agent15, `SectionAffineInverse.lean`). Under `3x+22r≡1 (mod 16)`, this predecessor has odd coordinates, right coordinate ≥5, and sum 4 mod 8. Agent34's **original-source** exact odd-four iff (`OddFourExactOriginal.lean`) then forces its predecessor `(b,c)` to satisfy `2b+4=x+6r-3` and `2c+3=b+2r-1`. Integer arithmetic forces `c≥5`, `c` odd, and `(b+c)%4=1`. The genuine initial section is `(5,1)`; at a positive section time this contradicts Agent3's **original-source** odd-image theorem (`Agent3CImage.lean`), which proves `(b+c)%4` must be 0 or 3 for odd `c≥5`. At `(16u+9,4)`, the first predecessor has right counter one, so Agent20's source `blank_right_one_iff_initial` excludes it.

**Exact status:** The new Lean original-import module references only these genuine existing source declarations and ordinary arithmetic. A local Lean 4.36.0-rc2 *contract-level composition check* redefined only the source theorem **signatures** as transparent **abstract assumptions** (outside the committed source file) and typechecked every complete composite proof, with no `sorry`. Its `#print axioms` consequently reported the imported abstract assumptions; **this does not certify the entire original-source import chain**. The source premises themselves have been proved by earlier agents and, where noted in their dossiers, original-source CI; the *new composite* still awaits compilation against actual original imports after the Actions runner outage. The committed `DoubleInverseOriginal.lean` contains no assumptions, copies or replacement definitions of source theorems and remains a pending source-integration proof.

An independent 200,000,000-section C++ screening of the exact source-equation projection found **zero** visits to any of the four cylinders and the known three left-one visits, while exactly matching the previously certified 150,052-return checkpoint. This is a valuable falsification stress test, **not evidence of the universal quantifiers**; the proof argument above is the actual basis for the proposed exclusions. The local C++ screen and 64 finite reverse closures are not yet separately committed since existing Agent11/34 inverse tools serve the same purpose.

**Novelty is uncertain.** These restrictions are direct corollaries of earlier original-source inverse and image lemmas. Other agents may already have equivalent excluded cylinders via M16/M32 quotients. They belong in `im-results/`, pending independent prior-art assessment and successful unchanged-source compilation. They exclude part of the infinite first-family stopping locus but cannot eliminate all four residue sectors, the remaining first-family points, or the two-parameter second halting family. BB(6) remains open.

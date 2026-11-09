# #746: certified logarithmic sweep address and source-exact same-band reset batching

**Agent 7, 9 November 2026. Intermediate exact algorithmic and symbolic research.** The source C-model reduction for the six-state machine `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` remains unresolved at the actual blank root `C(2,0)`. These theorems improve the authenticated reset evaluator and establish whole families of safe multi-reset steps. They prove neither halting nor nonhalting of the six-state machine and give no new BB(6) bound. External academic novelty is unassessed; retain under `im-results/`.

## Exact first-failed sweep in two candidates

Agent44's verified [`ScanFail.lean`](../agent44-746-rank/ScanFail.lean) scans the least index satisfying `h+k+5<8*2^k` sequentially from zero. Define

```
b = Nat.log2(h+5) - 2
bitFirst(h) = if h+b+5 < 8*2^b then b else b+1
```

[`SweepBitLength.lean`](SweepBitLength.lean) proves, **for every natural h**, that `bitFirst(h)` satisfies this failed guard and every earlier index does not. The proof uses the exact binary-log interval `2^(b+2)≤h+5<2^(b+3)` and proves that failure necessarily occurs by `b+1`. No heuristic estimate or finite cutoff is involved.

[`SweepBitLengthBridge.lean`](SweepBitLengthBridge.lean) establishes **`CascadeFastReturn.firstFailedK_eq_bit`** using Agent44's unchanged source theorem `firstFailedK_spec`. [`SweepBitOutcome.lean`](SweepBitOutcome.lean) defines `bitOutcome` with the new index and the original source arithmetic, then proves the exact equalities **`bitOutcome_eq_fastOutcome`** and **`runBit_eq_runFast`** for all starting heights and all finite reset counts. Its `bitOutcome_sound` inherits the original certified source `Outcome` predicate. This means the optimization changes no source path, halting outcome, or reachable reset height.

The new scanner uses one binary-length query and one possible correction, instead of up to Θ(log h) guard iterations. This is a number of candidate tests, not a claim of bit-complexity independent of input size.

## Entire safe blocks of consecutive even resets

Set `p=2^k`, `A=8p+k`, and define `H(k,m,d)=A-2^m*d` using natural subtraction. Theorems [`SweepEvenBlock.lean`](SweepEvenBlock.lean) and [`SweepEvenOrbit.lean`](SweepEvenOrbit.lean) prove **for all k,m,d** with

```
d ≥ 2*k+6
H(k,m,d) ≥ 4*2^k
```

the exact universal formula

```
∀ t ≤ m, runBit (H(k,m,d)) t = some (H(k,m-t,d)).
```

Every one of those t source-C first-return transitions is successful. The local first-failed index stays k on every earlier step and the source's exact even branch performs `H(k,r+1,d) -> H(k,r,d)`. In particular, m successful returns can be represented by one arithmetic endpoint certificate. For m=0 the statement is the trivial zero-step identity.

[`SweepEvenFamily.lean`](SweepEvenFamily.lean) supplies **arbitrarily long symbolic examples** with `k=2m+10` and `d=4m+26`, thereby proving the hypotheses for every m. They are **synthetically chosen C-reset starting heights**; they are not asserted reachable from the blank root.

[`SweepEvenOrbit.lean`](SweepEvenOrbit.lean) additionally defines `evenBlockCheck h k m d` as exact arithmetic and proves `evenBlockCheck_sound`. [`SweepMacroCheck.lean`](SweepMacroCheck.lean) defines `macroStep`: it accepts only a positive-length, checked proposed batch, otherwise it performs one ordinary `bitOutcome`. **`macroStep_sound`** proves for *arbitrary, even adversarial, proposed parameters* that its output is exactly `runBit h` for the reported number of actual reset edges. This interface can safely consume untrusted batch suggestions without enlarging the Lean trust base.

Two additional standalone theorems in `SweepBitLength.lean` establish monotonicity of the first-failed sweep level in h and that `u≥8*2^k` implies `firstFailIndex u>k`. They were locally kernel-checked after the full-source CI below; source CI should include them in its next run.

## Verification and reproducible experiments

- **Full unchanged checked-in C-source Lean 4.36.0-rc2 CI succeeded**: [run 42554748122](https://github.com/FlareZ123/bb6/actions/runs/42554748122), verifying the new binary sweep, original scanner bridge, exact successor and all finite trajectories; [run 42555858957](https://github.com/FlareZ123/bb6/actions/runs/42555858957), verifying the complete parametric one-step and m-step even-block formulas; and [run 42556422820](https://github.com/FlareZ123/bb6/actions/runs/42556422820), additionally verifying the all-prefix theorem, universally quantified arbitrary-length construction, arithmetic checker and macro soundness. The workflow compiles the original Agent10 reset semantics, Agent44's unchanged scanner and successor, and our modules with no proof-signature stubs. The arithmetic, all-prefix and checked-macro theorems use only `propext` and `Quot.sound`; the theorems inheriting source `firstFailedK_spec` and `fastOutcome_sound` also use the existing source dependency `Classical.choice`. No `sorryAx` or `native_decide` occurs.
- [`verify_fast_sweep.py`](verify_fast_sweep.py) compares the new sweep index with the old sequential scan for **every h below 100,000** plus 350 deterministic large-integer cases, and independently compares exact first outcomes against the original C-step map for **every h below 10,000**. All passed. On one local Python benchmark, sweep-index computation at 1,024, 8,192 and 65,536 input bits was approximately **323×, 4,273× and 46,408× faster**, respectively. These are environment-specific measurements and exclude the subsequent source successor arithmetic.
- [`verify_even_batches.py`](verify_even_batches.py) tests explicit families of lengths 1,3,10,100,1000; 500 deterministic random reset heights, including 236 valid checked batches; and the actual C(2,0) reset-prefix **10,000 returns**, all against ordinary one-reset iteration. The latter reproduced its exact 7,674-bit final height while using 2,513 validated batch operations covering 5,011 transitions, saving 2,498 ordinary `bitOutcome` calls; the longest observed batch was 10. At this moderate genuine-root horizon, prototype Python batch overhead slightly *exceeded* individual execution time. The improvement is a reusable algebraic and certified batching primitive, not a demonstrated end-to-end rooted search speedup.

## Research consequence and next target

The exact affine relation `H(k,r+1,d) -> H(k,r,d)` supplies a proof-carrying way to compress arbitrarily long same-k even-reset streaks. Combined with the prior genuine source theorem that odd-branch parents lie below `8*2^k` and their successors above that threshold ([`ResetRank.lean`](../agent44-746-rank/ResetRank.lean)), this suggests a **linear-in-sweep-scale bound on macro events**, even when the number of individual resets is quadratic in scale. A formal amortized macro event bound and a root-sensitive all-index fatal obstruction are still missing. Neither synthetic block length nor a finite blank-root simulation resolves the remaining infinite reachability question.

Run the already existing **manual-only** [Agent44 full first-return CI workflow](../../.github/workflows/agent44-746-fanin.yml) to repeat source checking; this invocation augmented that workflow with the new modules without introducing per-commit CI.

## The all-time dyadic address invariant and stage-length theorem

The further exact theorems in [`SweepBitLength.lean`](SweepBitLength.lean), [`SweepOddCross.lean`](SweepOddCross.lean), [`SweepAddress.lean`](SweepAddress.lean), [`SweepOrbitAddress.lean`](SweepOrbitAddress.lean), and [`SweepSameAddress.lean`](SweepSameAddress.lean) expose an all-orbit structural invariant. Define `K(h)=firstFailIndex(h)` and its upper-level deficit `D_k(h)=8*2^k+k-h`. For **every** successful source-C first-reset edge `h → u`, `K(h)≤K(u)`, and any odd-branch edge has `K(h)<K(u)`. Thus the actual blank-root source reset orbit visits successive dyadic address levels in nondecreasing order, with no return to an earlier level. If `K(h)=K(u)=k`, the edge is necessarily even and
```
D_k(h) = 2 * D_k(u).
```
This identity now holds even for low-band starting h: [`SweepEvenDeficit.lean`](SweepEvenDeficit.lean) obtains the nonhalting guard from the actual `bitOutcome h = some u` hypothesis.

[`SweepLevelBound.lean`](SweepLevelBound.lean) defines the authentic `SameLevelPath k h u m` relation as a finite sequence of genuine `bitOutcome` resets that remain in the same k level. Its universal theorems prove
```
D_k(h) = 2^m * D_k(u),
m ≤ Nat.log2(D_k(h)).
```
The second inequality holds because the original sweep failure guard gives `D_k(u)≥1`. Consequently **there is no infinite same-level source reset path**, regardless of synthetic or authentic start. Every infinite successful source orbit must therefore visit infinitely many increasing sweep levels. This is a mathematically exact structural consequence and still does not exclude a future fatal gate.

[`SweepEvenMaximal.lean`](SweepEvenMaximal.lean) establishes a companion terminal dichotomy for any maximal same-k even block with `D=2^m d` and `d≥2k+6`: its last d is odd or `d<4k+12`. The odd continuation moves to a larger k; the even continuation in this narrow strip also moves to a larger k, by the exact [`SweepEvenExit.lean`](SweepEvenExit.lean) upper-guard lemma. These component proofs motivate a future source-certified compressed event scheduler with a finite number of events per level. The algorithm integrating this classification with the low-band first step is not yet completely formalized.

Lean 4.36.0-rc2 kernel locally typechecked the new `SweepEvenDeficit`, `SweepAddress`, `SweepOrbitAddress`, `SweepSameAddress`, and `SweepLevelBound` modules, plus the `SweepEvenMaximal` lemma, with no `sorry`. The complete unchanged-source CI [42558004880](https://github.com/FlareZ123/bb6/actions/runs/42558004880) successfully checked the earlier arithmetic/odd/exit/maximal modules. The latest combined source CI for the additional all-time address and stage-length files should be checked independently before treating those additions as full-source certified.

## Fatal gates occur only upon entering a new level

A further all-time source-trajectory theorem in [`SweepGateEntry.lean`](SweepGateEntry.lean) exposes a root-relevant consequence. Define `fatalAt(h)` as the exact source halting condition `h+K(h)+4=4*2^{K(h)}`. The universal low-guard inequality `4*2^{K(h)}≤h+K(h)+4` means a fatal height is the **minimal admissible source reset height at its own level**.

For every genuinely successful edge `bitOutcome(h)=some(u)`, Lean proves:
```
fatalAt(u) → K(h) < K(u).
```
Indeed, if the level were unchanged, the already proved strict height increase from h to u and the lower-bound guard at h make equality with the fatal height impossible. Therefore **the first reset in each newly entered level is its only possible fatal reset**. Subsequent same-level even returns are safe with respect to that level's fatal trigger. This reduces the infinite halting question to the trajectory's level-entry events, a potentially smaller exact deterministic subsystem. It does not establish that those entry events avoid the unique fatal height.

The gate-entry statement passed local Lean 4.36.0-rc2 checking without `sorry`; a combined full checked-in-source CI run has been requested separately. Do not treat local-only proof as an externally verified machine-halting decision.

# Cryptid #623: weighted ternary potential and sharp conditional pair gain

**Status (2026-11-04):** Weighted-potential, source-verified small-output bound, and five infinite affine rays have passed original-source GitHub Actions. A stronger universal **27-unit two-return** claim is formalized in Lean but **awaits full original-source validation**. No halting/nonhalting conclusion is established.

## Model and authentication

We use the unmodified pinned DeepMind Cryptids [#623 Lean accelerator](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean), source revision `c86f15861709b76042998c5211c7b2f83991621b`. Its high-level map is `T=highLevelNext`, with state `D(a,d)` and genuine blank start `D(0,7)`.

**Source-verified** `WeightedPotentialSource.lean`, [CI 41889267609](https://github.com/FlareZ123/bb6/actions/runs/41889267609): Every successful ternary evaluator has

```
evalA a k m = some (aa,bb,dd)  =>  2*a+m <= 2*aa+bb+dd.
```

Every successful complete B-drain has

```
drainB a b d = some (D aa dd)  =>  2*a+b+d <= 2*aa+dd;
and if b>0,  2*a+d+2*b+3 <= 2*aa+dd.
```

This weighted inequality captures first-counter consumption and second-counter output jointly, strengthening the unweighted mass budget. Source CI `#print axioms` reports only `propext` and `Quot.sound`.

**Source-verified** `SmallOutputGainSource.lean` and `FixedRaysSource.lean`, [CI 41891175943](https://github.com/FlareZ123/bb6/actions/runs/41891175943): For even `a>=6`, positive `d`, `a+d>=100`, and a successful output `T(D(a,d))=D(b,e)` with `b<=4`, the total mass gain is at least **20**. Five infinite far-left affine rays have verified lower bounds:

| Fixed second counter d | Threshold on first counter a | One-step mass gain at least |
|---|---:|---:|
| 7 | 23 | 20 |
| 9 | 27 | 20 |
| 10 | 25 | 18 |
| 12 | 29 | 24 |
| 14 | 33 | 28 |

These rays use Agent8's original-source first-counter transport. The `next_output_second_two` lemma was appended later and awaits the latest CI.

## Proposed full two-step theorem (pending full CI)

The current files `TwoStep27HighSource.lean`, `LowStepSource.lean`, `TwoStep27Source.lean`, and `Finite27Source.lean` aim to prove, for **every** even `a` and every `d`, with `a+d>=23`, that any two successful transitions

```
T(D(a,d))=some(D(b,e)),
T(D(b,e))=some(D(c,f))
```

satisfy `a+d+27<=c+f`. The proof splits at mass 100.

For mass at least 100: if `a>=6,d>0`, a successor with first counter `b<=4` gains at least 20 on the first step and at least 7 on the second. If `b>=6`, the two original-source Agent8 14-unit bounds each contribute, giving at least 28. The `d=0` ray and all `a=0,2,4` inputs reduce to explicit source-checked one-step formulas and existing affine rays; see `LowStepSource.lean`.

For `23<=a+d<100`: an independently executed Lean 4.36.0-rc2 kernel certificate for the exact source-matched recurrence, with `Fin 100` coordinates and `by decide +kernel`, proved every relevant two-step pair obeys 27. `Finite27Source.lean` repeats the certificate against direct imported source and still needs original-source CI.

The finite-strip threshold 23 is sharp as well: from `D(12,10)` (mass 22), the exact two-step orbit is `D(12,10) -> D(2,38) -> D(38,9)`, gaining only 25. The revised `Finite27Source.lean` includes this source-reflection counterexample and a local Lean4.36 kernel verification of the enlarged mass 23–99 strip, pending full pinned-source CI.

The constant is **sharp on the actual blank-origin orbit** according to exact model computation:

```
run 4 = D(2,83)    mass 85
run 5 = D(84,10)   mass 94
run 6 = D(74,38)   mass 112
```

The transition from `run 4` to `run 6` gains exactly 27. `Finite27Source.lean` includes `by decide +kernel` proofs of these equalities, pending original-source CI. The proposed conditional root consequences are `run(4+2k)` mass at least `85+27k` and `run(5+2k)` mass at least `94+27k`, whenever those states survive.

Source CI workflow: [agent49-623-parity-source.yml](https://github.com/FlareZ123/bb6/blob/main/.github/workflows/agent49-623-parity-source.yml). The latest corrected run should be checked before treating the 27-unit statement as authenticated; earlier failures were CI runner disk quota or Lean tactics/source-dependency assembly, never a mathematical counterexample. Original source uses Lean 4.35.0-rc4; standalone mirror used Lean 4.36.0-rc2. All proof claims are *conditional on successful accelerator returns*. There is no proof of #623 blank-origin nonhalting or exact BB(6).

## Independent replication and outstanding concerns

- Verify exact source imports and inspect `#print axioms` for every theorem; `sorryAx` invalidates a claim.
- The original Agent8 `SharpMass21LowSource.lean` currently has a dangling theorem documentation comment at line 70, causing source CI to fail if imported; our branch-combination lemma directly imports prior source-verified +14 modules and avoids this dependency. Agent8 notified.
- Mathematical scope: growing counter mass does not exclude a future halting event in a thin arithmetic gate. The exact blank-root fate and BB(6) remain unresolved.


## Original-source certification completed: 2026-11-04 23:38 UTC

**The preceding CI-pending caveats are superseded.** Agent 48 repaired two Lean proof-elaboration issues in the reused original-source modules: a private-`next` abbreviation prevented source-exact `high_zero_exact` rewriting in `TwoStep27Source.lean`, and a fixed ray needed the explicitly proved weakening `24≤d → 23≤d` in `Sharp27RaySource.lean`.

Unmodified pinned Cryptids original-source [GitHub Actions run **41934412699**](https://github.com/FlareZ123/bb6/actions/runs/41934412699) **completed successfully**. All proof steps passed, including `TwoStep27HighSource.lean`, `TwoStep27Source.lean`, `Finite27Source.lean`, and `Sharp27RaySource.lean`; the audited final theorems show only standard `propext`, `Classical.choice`, and `Quot.sound` axioms, no `sorryAx`. Consequently the entire **sharp all-even, all-input, two-successful-step mass gain ≥27 for mass≥23**, the infinite exact equality rays, and the genuine blank-start conditional ≥27 pair slopes are now **directly original-source certified**. They remain conditional on surviving returns and do not prove #623 halts or runs forever. This closes the specific source-integrity gap described in the previous Critic failure communication.

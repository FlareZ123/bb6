# Machine #746: certified dyadic level macro, quadratic rank, and alternating high-level exits

**Agent 7 · 9 November 2026 · intermediate rigorous research.** Machine `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` is an unresolved six-state, two-symbol Busy Beaver candidate. The authenticated first-return model has the actual blank-origin post-initial source reset `C(2,0)`. The results here are **theorems about the unchanged source first-return arithmetic for every natural reset height**, with full original-source Lean 4.36.0-rc2 builds. They are not a halt/nonhalt proof for the actual blank tape, do not bound BB(6) globally, and do not establish an exact BB(6) value.

## 1. Exact constant-candidate sweep and original-source semantics

Set

```text
K(h) = least k with h+k+5 < 8·2^k.
b(h) = log₂(h+5) - 2 (natural subtraction).
K(h) = b(h) if h+b(h)+5 < 8·2^b(h), else b(h)+1.
```

The final equality holds **for all h**, not just a finite range. [SweepBitLength.lean](SweepBitLength.lean) proves the least-failure guard, and [SweepBitLengthBridge.lean](SweepBitLengthBridge.lean) identifies it with the unchanged source-certified scanner of [Agent 44](../agent44-746-rank/README.md). [SweepBitOutcome.lean](SweepBitOutcome.lean) proves `bitOutcome h = fastOutcome h` and `runBit h n = runFast h n` for every finite n. Here `bitOutcome` returns `none` exactly at the source fatal gate `h+K(h)+4=4·2^K(h)`. Every statement below uses this authenticated semantics.

The binary-length method tests at most two candidate indices, rather than sweeping up to K(h) by one-unit increments. This is an arithmetic index-search improvement, without a claim of constant bit complexity.

## 2. All-time source level dynamics

Write `k=K(h)`, `p=2^k`, `D_k(h)=8p+k-h`. For every source reset height,

```text
D_k(h) ≥ 2k+6.
```

For every successful first reset `bitOutcome h = some u`, [SweepAddress.lean](SweepAddress.lean), [SweepOddCross.lean](SweepOddCross.lean), [SweepEvenDeficit.lean](SweepEvenDeficit.lean), [SweepExactLevel.lean](SweepExactLevel.lean), and [SweepSameAddress.lean](SweepSameAddress.lean) establish:

- `h<u` and `K(h)≤K(u)`, with strict level increase on every odd-branch edge;
- if the edge is even, `D_k(h)=2D_k(u)`, including when the successor advances to another level;
- for even edges, **`K(u)=k` if and only if `D_k(h)≥4k+12`**, while **`K(u)=k+1` if and only if `D_k(h)<4k+12`**. In particular, no even edge skips a level.

[**SweepLevelBound.lean**](SweepLevelBound.lean) proves for every authentic sequence of m same-level edges from h to u that `D_k(h)=2^m·D_k(u)`, hence `m≤log₂(D_k(h))`. This forbids infinite trajectories trapped at any fixed level. [SweepGateEntry.lean](SweepGateEntry.lean) proves a reached fatal state can only be the **first entry at a new level**, as fatal heights are the minimal admissible heights at their own level.

## 3. Constructive, complete one-event-per-level normal form

Unlike the earlier [sufficient prepared even-block theorem](SweepEvenOrbit.lean), the following result covers **all nonfatal source heights**, including the source low band.

For `h` nonfatal, set `k=K(h)` and `D=D_k(h)`. Repeatedly divide D by two while D is even and its half remains at least `2k+6`. This uniquely produces

```text
D = 2^m d,
d ≥ 2k+6,
(d odd) or (d < 4k+12).
```

Then **the first m source resets succeed**, remain at level k, and have the exact endpoint

```text
u = 8·2^k+k-d.
```

The following one source reset either halts or advances to a strictly greater K. Thus one exact arithmetic batch and one terminal reset process an entire level. [SweepFullLevelBatch.lean](SweepFullLevelBatch.lean) proves existence and all-prefix safety, while [SweepStageAlgorithm.lean](SweepStageAlgorithm.lean) defines the total executable `terminalPair` and `levelMacro`, proving:

```lean
runBit h (levelMacro h).1 = (levelMacro h).2

levelMacro h = (count, some v) →
  firstFailIndex h < firstFailIndex v
```

[**SweepMacroOrbit.lean**](SweepMacroOrbit.lean) composes arbitrarily many such batches without changing source semantics. Its `macroOrbit_sound` proves `runBit start (macroOrbit start n).1 = (macroOrbit start n).2` for every n and arbitrary start, and `macroOrbit_level_bound` shows that n completed successful level events increase K by at least n. The returned count is the exact number of original source first resets, even when a batch contains many.

An independent positive [checker for user-supplied even batches](SweepMacroCheck.lean) is retained for adversarial proposal verification. [SweepEvenFamily.lean](SweepEvenFamily.lean) produces synthetic safe blocks of arbitrary length; those starts have **no asserted blank-root reachability**.

## 4. Quantitative universal forward rank

[**SweepQuadraticRank.lean**](SweepQuadraticRank.lean) defines

```text
W(0)=0,  W(k+1)=W(k)+k+4,
R(h)=W(K(h))+K(h)+4-log₂(D_{K(h)}(h)).
```

The natural subtraction in R never saturates: the proof establishes `log₂ D≤K+3`, so

```text
W(K(h))+1 ≤ R(h) ≤ W(K(h)+1).
```

For a successful same-level reset, R increases **exactly one**. Every successful reset, including an odd multilevel jump, increases R strictly. Consequently the source-checked theorem `successful_run_quadratic_level_bound` states:

```text
runBit start n = some u and K(u)≤L
    ⇒ n≤W(L+1) = Σ_{k=0}^L(k+4) = (L+1)(L+8)/2.
```

This is an **all-time halt-or-escape bound** below a given finite dyadic level, for arbitrary starts, not a global bound on the time until halt. It refines the related quadratic *backward* chain-depth ranking in [Agent 44](../agent44-746-rank/README.md), and does not rule out an orbit with unbounded K.

## 5. Exact fatal-entry arithmetic and all high-level two-even exclusion

Let `F_j=4·2^j-j-4` denote the source fatal height at level j, subject to the authentic source's admissibility conditions. [SweepAdjacentFatal.lean](SweepAdjacentFatal.lean) proves any successful even adjacent-level entry into fatal `F_(k+1)` has the uniquely forced parent deficit `D_k=4k+10`. If an earlier entry into k is followed by m genuine same-level resets before the final fatal even exit, its initial deficit must have been `2^m(4k+10)`.

[**SweepNoEvenEvenFatal.lean**](SweepNoEvenEvenFatal.lean) proves the source-exact initial entry interval: each even exit from level j into j+1 arrives at a height x with

```text
D_(j+1)(x)=2^(j+3)+c,     j+4 ≤ c ≤ 2j+6.
```

For every k≥8 and 0<c≤2k+4, the source-certified arithmetic theorem [`no_small_dyadic_factor`](SweepAlternatingExits.lean) excludes the much broader equation

```text
2^(k+2)+c = 2^m d
whenever m≥0 and 1≤d≤4k+10.
```

The proof combines a uniform exponential-versus-quadratic bound with dyadic divisibility. Since `2^m` divides the large power and the sum, it must divide c. The equation also forces `c<2^m`, which is impossible for positive c.

The stronger Lean theorem **`no_consecutive_even_level_exits`** in [SweepAlternatingExits.lean](SweepAlternatingExits.lean) establishes, with no fatality assumption:

```text
level j --successful even exit--> level j+1
        --m arbitrary genuine same-level resets-->
level j+1 --successful even exit--> level j+2
   is impossible for ALL j≥7 and m≥0.
```

Thus the previous fatal-specific theorem `no_even_then_even_fatal` is a special consequence of an all-trajectory high-level alternation constraint, rather than the strongest remaining result.

The [**SweepOddAfterEven.lean**](SweepOddAfterEven.lean) executable corollary strengthens the forward description. After every successful even entry into k≥8, the exact `terminalPair` factorization `D=2^m d` yields **d odd and d>4k+10**. Therefore, for a nonfatal level entry, the next successful level exit must use the odd branch.

The [**SweepShortEvenEntry.lean**](SweepShortEvenEntry.lean) path theorem provides a stronger quantitative bound: for any authentic m-edge same-k path beginning immediately after such an even entry,

```text
m ≤ floor(log₂(2k+4)),   k≥8.
```

This is logarithmic in k rather than the generic linear bound `m≤k+3`. It follows from exact deficit doubling, the short c interval, and the fact that `2^m` must divide c. Every statement is quantified over arbitrary source starting heights and all finite same-level histories; genuine blank-root reachability is neither assumed nor proved.

The [**exact high-band odd-image criterion**](../agent7-746-fatal-depth-27/README.md) sharpens the preceding odd-entry analysis for all source heights, independently of blank-root reachability. At level k≥2, for any entry e≥6·2^k, existence of an odd source first-reset predecessor is **equivalent to** `27∣(2e+5)` when `4e+10<27·2^k`, and equivalent to `9∣(2e+5)` in the complementary upper band. Both converses construct exact odd source parents with valuations t=2 and t=1. In the narrow interval, an odd entry followed by m same-level resets and an adjacent even fatal exit additionally forces the **unique** m%18 class determined by k%54, strengthening the previous mod-9 depth sieve. The full original-source Lean [CI 42593843110](https://github.com/FlareZ123/bb6/actions/runs/42593843110) passes with standard axioms only. The classification is for genuine source edges from arbitrary heights; synthetic ancestors are not certified blank-reachable.

**Unresolved boundary:** even-entry stages have been sharply constrained and the high-band odd image is now exactly characterized, but odd exits may skip multiple levels, and the authentic blank-reset orbit might still hit a valid fatal height through a surviving odd-entry history. No general nonhalting theorem follows.

## 6. Original-source verification and reproducibility

Manual-only [Lean 4.36.0-rc2 source-audit workflow](../../.github/workflows/agent44-746-fanin.yml) compiles the unchanged original first-return definitions, original scanner/valuation proofs, and these modules without synthetic source stubs or `sorry`:

| Checked result | Original-source successful CI |
|---|---|
| Logarithmic scanner and unchanged-source equality | [42554748122](https://github.com/FlareZ123/bb6/actions/runs/42554748122) |
| Arbitrarily long checked even batches and sound macro checker | [42556422820](https://github.com/FlareZ123/bb6/actions/runs/42556422820) |
| All-time address, stage depth and gate-entry lemmas | [42558752657](https://github.com/FlareZ123/bb6/actions/runs/42558752657) |
| Exact even-level criterion, adjacent fatal necessary deficit, stage normal form | [42561377599](https://github.com/FlareZ123/bb6/actions/runs/42561377599) |
| Executable `levelMacro` soundness and advancement | [42562041732](https://github.com/FlareZ123/bb6/actions/runs/42562041732) |
| Arbitrary-length composed macro soundness | [42562419865](https://github.com/FlareZ123/bb6/actions/runs/42562419865) |
| Strict integer forward rank and quadratic bound | [42562691497](https://github.com/FlareZ123/bb6/actions/runs/42562691497) |
| Initial high-level two-even fatal-history exclusion | [42563450899](https://github.com/FlareZ123/bb6/actions/runs/42563450899) |
| All-index ban on consecutive successful even level exits | [42564354336](https://github.com/FlareZ123/bb6/actions/runs/42564354336) |
| Odd terminal residual and logarithmic same-level bound after even entry | [42564766777](https://github.com/FlareZ123/bb6/actions/runs/42564766777) |
| Exact high-band odd image iff and narrow-entry mod-27 fatal-depth sieve | [42593843110](https://github.com/FlareZ123/bb6/actions/runs/42593843110) |

All newly checked proof conclusions audit with ordinary Lean axioms `propext`, `Quot.sound`, and where imported source/executable recursion requires it, `Classical.choice`. No `sorryAx` is used. The transient failed run 42560897705 identified a missing local import of `fatalAt`; the module was corrected and subsequently passed unchanged-source CI.

The preserved standalone regression scripts [verify_fast_sweep.py](verify_fast_sweep.py) and [verify_even_batches.py](verify_even_batches.py) compare finite arithmetic outcomes against the earlier scanner and original C-map, including an authenticated 10,000-reset root prefix. These tests are sanity checks; the unbounded claims above are proved symbolically.

## Remaining mathematical objective

A halt of the authentic six-state machine is still equivalent to a blank-root C-reset hitting one of infinitely many eligible `F_j`. The all-level macro, strictly rising rank, exact even-entry odd-next-branch theorem, and high-level alternation obstruction now reduce the undecided domain to **level-entry transitions with surviving odd-entry or odd-jump histories** and exceptional low-level cases. A useful next proof would characterize the actual root's odd exits strongly enough to exclude the surviving level-entry deficits, or produce a fully source-connected genuine halt witness. Longer cutoffs of the same unchanged orbit do not establish this.

The results belong in `im-results/` until their external originality and publishability have been assessed. Neither this dossier nor any other current project result determines BB(6).

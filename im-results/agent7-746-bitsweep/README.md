# Machine #746: source-exact dyadic level compression and fatal-history obstruction

**Agent 7 · 9 November 2026 · intermediate rigorous research.** Machine \`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA\` is an unresolved six-state, two-symbol Busy Beaver candidate. The authenticated first-return model has the actual blank-origin post-initial source reset \`C(2,0)\`. The results here are **theorems about the unchanged source first-return arithmetic for every natural reset height**, with full original-source Lean 4.36.0-rc2 builds. They are not a halt/nonhalt proof for the actual blank tape, do not bound BB(6) globally, and do not establish an exact BB(6) value.

## 1. Exact constant-candidate sweep and original-source semantics

Set

\`\`\`text
K(h) = least k with h+k+5 < 8·2^k.
b(h) = log₂(h+5) - 2 (natural subtraction).
K(h) = b(h) if h+b(h)+5 < 8·2^b(h), else b(h)+1.
\`\`\`

The final equality holds **for all h**, not just a finite range. [SweepBitLength.lean](SweepBitLength.lean) proves the least-failure guard, and [SweepBitLengthBridge.lean](SweepBitLengthBridge.lean) identifies it with the unchanged source-certified scanner of [Agent 44](../agent44-746-rank/README.md). [SweepBitOutcome.lean](SweepBitOutcome.lean) proves \`bitOutcome h = fastOutcome h\` and \`runBit h n = runFast h n\` for every finite n. Here \`bitOutcome\` returns \`none\` exactly at the source fatal gate \`h+K(h)+4=4·2^K(h)\`. Every statement below uses this authenticated semantics.

The binary-length method tests at most two candidate indices, rather than sweeping up to K(h) by one-unit increments. This is an arithmetic index-search improvement, without a claim of constant bit complexity.

## 2. All-time source level dynamics

Write \`k=K(h)\`, \`p=2^k\`, \`D_k(h)=8p+k-h\`. For every source reset height,

\`\`\`text
D_k(h) ≥ 2k+6.
\`\`\`

For every successful first reset \`bitOutcome h = some u\`, [SweepAddress.lean](SweepAddress.lean), [SweepOddCross.lean](SweepOddCross.lean), [SweepEvenDeficit.lean](SweepEvenDeficit.lean), [SweepExactLevel.lean](SweepExactLevel.lean), and [SweepSameAddress.lean](SweepSameAddress.lean) establish:

- \`h<u\` and \`K(h)≤K(u)\`, with strict level increase on every odd-branch edge;
- if the edge is even, \`D_k(h)=2D_k(u)\`, including when the successor advances to another level;
- for even edges, **\`K(u)=k\` if and only if \`D_k(h)≥4k+12\`**, while **\`K(u)=k+1\` if and only if \`D_k(h)<4k+12\`**. In particular, no even edge skips a level.

[**SweepLevelBound.lean**](SweepLevelBound.lean) proves for every authentic sequence of m same-level edges from h to u that \`D_k(h)=2^m·D_k(u)\`, hence \`m≤log₂(D_k(h))\`. This forbids infinite trajectories trapped at any fixed level. [SweepGateEntry.lean](SweepGateEntry.lean) proves a reached fatal state can only be the **first entry at a new level**, as fatal heights are the minimal admissible heights at their own level.

## 3. Constructive, complete one-event-per-level normal form

Unlike the earlier [sufficient prepared even-block theorem](SweepEvenOrbit.lean), the following result covers **all nonfatal source heights**, including the source low band.

For \`h\` nonfatal, set \`k=K(h)\` and \`D=D_k(h)\`. Repeatedly divide D by two while D is even and its half remains at least \`2k+6\`. This uniquely produces

\`\`\`text
D = 2^m d,
d ≥ 2k+6,
(d odd) or (d < 4k+12).
\`\`\`

Then **the first m source resets succeed**, remain at level k, and have the exact endpoint

\`\`\`text
u = 8·2^k+k-d.
\`\`\`

The following one source reset either halts or advances to a strictly greater K. Thus one exact arithmetic batch and one terminal reset process an entire level. [SweepFullLevelBatch.lean](SweepFullLevelBatch.lean) proves existence and all-prefix safety, while [SweepStageAlgorithm.lean](SweepStageAlgorithm.lean) defines the total executable \`terminalPair\` and \`levelMacro\`, proving:

\`\`\`lean
runBit h (levelMacro h).1 = (levelMacro h).2

levelMacro h = (count, some v) →
  firstFailIndex h < firstFailIndex v
\`\`\`

[**SweepMacroOrbit.lean**](SweepMacroOrbit.lean) composes arbitrarily many such batches without changing source semantics. Its \`macroOrbit_sound\` proves \`runBit start (macroOrbit start n).1 = (macroOrbit start n).2\` for every n and arbitrary start, and \`macroOrbit_level_bound\` shows that n completed successful level events increase K by at least n. The returned count is the exact number of original source first resets, even when a batch contains many.

An independent positive [checker for user-supplied even batches](SweepMacroCheck.lean) is retained for adversarial proposal verification. [SweepEvenFamily.lean](SweepEvenFamily.lean) produces synthetic safe blocks of arbitrary length; those starts have **no asserted blank-root reachability**.

## 4. Quantitative universal forward rank

[**SweepQuadraticRank.lean**](SweepQuadraticRank.lean) defines

\`\`\`text
W(0)=0,  W(k+1)=W(k)+k+4,
R(h)=W(K(h))+K(h)+4-log₂(D_{K(h)}(h)).
\`\`\`

The natural subtraction in R never saturates: the proof establishes \`log₂ D≤K+3\`, so

\`\`\`text
W(K(h))+1 ≤ R(h) ≤ W(K(h)+1).
\`\`\`

For a successful same-level reset, R increases **exactly one**. Every successful reset, including an odd multilevel jump, increases R strictly. Consequently the source-checked theorem \`successful_run_quadratic_level_bound\` states:

\`\`\`text
runBit start n = some u and K(u)≤L
    ⇒ n≤W(L+1) = Σ_{k=0}^L(k+4) = (L+1)(L+8)/2.
\`\`\`

This is an **all-time halt-or-escape bound** below a given finite dyadic level, for arbitrary starts, not a global bound on the time until halt. It refines the related quadratic *backward* chain-depth ranking in [Agent 44](../agent44-746-rank/README.md), and does not rule out an orbit with unbounded K.

## 5. Exact fatal-entry arithmetic and unbounded two-even obstruction

Let \`F_j=4·2^j-j-4\` be the source fatal height at level j, subject to the source's actual admissibility constraints. [SweepAdjacentFatal.lean](SweepAdjacentFatal.lean) proves that **any successful even reset from level k into its adjacent fatal height \`F_(k+1)\`** has the unique old deficit

\`\`\`text
D_k(parent)=4k+10.
\`\`\`

If the orbit spent m previous genuine same-level resets after entering that level, its **level-entry deficit** must be \`2^m(4k+10)\`.

[**SweepNoEvenEvenFatal.lean**](SweepNoEvenEvenFatal.lean) establishes a further infinite exclusion. Every successful even exit from level j to j+1 arrives at a level-entry height x satisfying

\`\`\`text
D_(j+1)(x) = 2^(j+3)+c,  j+4≤c≤2j+6.
\`\`\`

Set \`k=j+1\`. For every \`k≥8\`, the number \`2^(k+2)+c\`, where \`0<c≤2k+4\`, **cannot** equal \`2^m(4k+10)\` for any m. The proof bounds the necessary 2-adic factor using \`(2k+4)(2k+5)<2^(k+1)\`, then derives an impossible divisibility \`2^m∣c\` while \`0<c<2^m\`.

Therefore the formal theorem \`no_even_then_even_fatal\` excludes **every** history of the following source-exact shape, uniformly in m:

\`\`\`text
level j --even exit--> level j+1
        --m genuine same-level resets-->
level j+1 --even exit--> fatal at level j+2,
for every j≥7.
\`\`\`

The result excludes an infinite structured family of fatal paths. It makes **no assertion** that an earlier odd exit, an odd multilevel fatal jump, or an initial low-level exceptional history is impossible. The actual blank-root orbit may contain these alternatives.

## 6. Original-source verification and reproducibility

Manual-only [Lean 4.36.0-rc2 source-audit workflow](../../.github/workflows/agent44-746-fanin.yml) compiles the unchanged original first-return definitions, original scanner/valuation proofs, and these modules without synthetic source stubs or \`sorry\`:

| Checked result | Original-source successful CI |
|---|---|
| Logarithmic scanner and unchanged-source equality | [42554748122](https://github.com/FlareZ123/bb6/actions/runs/42554748122) |
| Arbitrarily long checked even batches and sound macro checker | [42556422820](https://github.com/FlareZ123/bb6/actions/runs/42556422820) |
| All-time address, stage depth and gate-entry lemmas | [42558752657](https://github.com/FlareZ123/bb6/actions/runs/42558752657) |
| Exact even-level criterion, adjacent fatal necessary deficit, stage normal form | [42561377599](https://github.com/FlareZ123/bb6/actions/runs/42561377599) |
| Executable \`levelMacro\` soundness and advancement | [42562041732](https://github.com/FlareZ123/bb6/actions/runs/42562041732) |
| Arbitrary-length composed macro soundness | [42562419865](https://github.com/FlareZ123/bb6/actions/runs/42562419865) |
| Strict integer forward rank and quadratic bound | [42562691497](https://github.com/FlareZ123/bb6/actions/runs/42562691497) |
| All-index high-level two-even fatal-history exclusion | [42563450899](https://github.com/FlareZ123/bb6/actions/runs/42563450899) |

All newly checked proof conclusions audit with ordinary Lean axioms \`propext\`, \`Quot.sound\`, and where imported source/executable recursion requires it, \`Classical.choice\`. No \`sorryAx\` is used. The transient failed run 42560897705 identified a missing local import of \`fatalAt\`; the module was corrected and subsequently passed unchanged-source CI.

The preserved standalone regression scripts [verify_fast_sweep.py](verify_fast_sweep.py) and [verify_even_batches.py](verify_even_batches.py) compare finite arithmetic outcomes against the earlier scanner and original C-map, including an authenticated 10,000-reset root prefix. These tests are sanity checks; the unbounded claims above are proved symbolically.

## Remaining mathematical objective

A halt of the authentic six-state machine is still equivalent to a blank-root C-reset hitting one of infinitely many eligible \`F_j\`. The all-level macro, rank, and two-even obstruction now reduce the undecided domain to **level-entry transitions with surviving odd-entry or odd-jump histories** and exceptional low-level cases. A useful next proof would classify the genuine root's odd exits strongly enough to exclude the surviving level-entry deficits, or produce a fully source-connected genuine halt witness. Longer cutoffs of the same unchanged orbit do not establish this.

The results belong in \`im-results/\` until their external originality and publishability have been assessed. Neither this dossier nor any other current project result determines BB(6).

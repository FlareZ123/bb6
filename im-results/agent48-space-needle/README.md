# Agent 48: Space Needle (BMO6) exact single-counter arithmetic normal form

**Status:** intermediate original-source-checked algebraic reduction for the unresolved BB(6) Space Needle holdout. It does **not** decide whether the original machine halts, determine BB(6), or prove a new lower bound. No external priority claim.

Machine: `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`.

## Published source and verification

Google DeepMind Cryptids published the machine with a certified high-level `HighLevelState.N d` representation, starting at `N(1)` from the **original blank tape**; it proves `IsHalt target ↔ CollatzHalts highLevelNext highLevelStart`. Their exact repository is pinned to `ced8f9f44f67a167d5ecc03e687b048c67926371`, source `BusyBeaver/BB6/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean`.

Our original-source Lean proof is [SpaceNeedleClosed.lean](./SpaceNeedleClosed.lean). The manual-only workflow [agent48-space-needle.yml](../../.github/workflows/agent48-space-needle.yml) restores the **unmodified original upstream** and its Mathlib dependencies, builds the published target module with its pinned Lean 4.35.0-rc4, and compiles our imported proof.

The first source-check [run 41428740035](https://github.com/FlareZ123/bb6/actions/runs/41428740035) **succeeded**, with only standard axioms for all seven theorems in the original version. The subsequently added elementary power-of-two/factorization identities were also compiled against locally reproduced exact definitions with Lean 4.36.0-rc2 and standard axioms only; a refreshed original-source CI run is being separately checked.

## Complete exact one-step map

Define `H(0)=0`, `H(k+1)=2(H(k)+1)`; define `O(q,0)=2q+1`, `O(q,k+1)=2(O(q,k)+1)`. For all natural `k,q`:

```text
H(k)+2 = 2^(k+1)
O(q,k)+2 = 2^k * (2q+3).
```

These families partition **all** natural counters. The source-level `scanEven` function has exact formulas, for every arbitrary accumulated counter `b`:

```text
scanEven(H(k), b) = none
scanEven(O(q,k), b) =
    some(N(b + O(q,k) + k + 3(q+1))).
```

Consequently, writing `v=v₂(d+2)`, `u=(d+2)/2^v` odd:

- The next high-level call halts exactly when `u=1`, equivalently `d+2` is a power of two.
- Otherwise, `u≥3` and `d' = d + v + 3(u-1)/2`. In particular every successful high-level return strictly increases the counter `d`. Any nonterminating high-level orbit is strictly increasing, hence cannot enter a cycle.

The formal theorem `scanEven_none_iff` is exact for every natural `d,b`, `scanEven_classification` establishes the total algebraic partition, and `highLevelNext_strict` establishes the strict step growth. These are globally quantified statements about the published original high-level transition, rather than a finite simulation.

## Blank-start experiment and limitations

Independent exact-bigint Python implementation from `d₀=1` checked **30,000 high-level successor calls** with no power-of-two terminal input. The final counter had 28,098 bits. This is exploratory evidence only. It is vastly shorter than many existing external computations, and should not be presented as a novelty or meaningful Busy Beaver lower bound.

**Unresolved decisive question:** does the particular recursively defined growing sequence `d₀=1`, `dₙ₊₁ = dₙ + v₂(dₙ+2) + 3((dₙ+2)/2^v-1)/2` ever land on `dₙ=2^k-2`? This exact arithmetic statement, combined with the original published machine/acceleration theorem, is equivalent to the genuine blank-tape halting problem for this holdout.

Future work: investigate 2-adic restrictions on this specific blank orbit, search a closed invariant excluding power-of-two hits, or construct a genuine finite witness. Generic growth and finite prefix checks are insufficient to decide halting.


## Later source-mirrored mathematical tools (2026-11-03)

- [TERMINAL-RESIDUES.md](TERMINAL-RESIDUES.md): locally kernel-verified exact original high-level predecessor existence for every decimal suffix of the power-of-two terminal exponent. For any \`a,r,B\` with \`r<10^a\`, there is \`K≥B\`, \`K%10^a=r\`, and at least one **unrestricted high-level** immediate predecessor to \`N(2^K−2)\`. Quantification covers all a. This is a negative method result for unconditional all-state modular predecessor exclusions, and **does not imply blank-tape reachability**. Source-mirrored local Lean has only standard axioms; original-source CI bridge remains pending the runner incident.
- [ODD-BLOCKS.md](ODD-BLOCKS.md): exact \`t\`-call high-level acceleration from \`N(2^t*m−1)\` to \`N(5^t*m−1)\` for positive m; if m odd, this is the complete maximal odd run. A terminal directly after this block requires \`5^t ∣ 2^K−1\`. Locally checked in Lean against literally pinned upstream high-level definitions with standard axioms. Full-source CI similarly pending.

Neither tool closes Space Needle, certifies an actual blank-root halting runtime, or establishes BB(6).

## 2026-11-04 source-connected two-step odd-terminal inverse

[`TWO-STEP-ODD.md`](TWO-STEP-ODD.md) gives an exact all-natural, source-connected conditional two-step terminal predecessor criterion: from `oddTower q v` through **one odd intermediate** to terminal `2^K-2` iff `2^(K+1)=5*(2^(v+1)+3)*q+15*2^v+5*v+12` for `K>0`. It proves fixed-`(K,v)` parameter uniqueness and `v<K`.

**Pinned original Cryptids source [CI 41931806607](https://github.com/FlareZ123/bb6/actions/runs/41931806607) passed** on 2026-11-04, compiling `SpaceNeedleOddBlocksSource.lean`, `NeedleTwoStepOdd.lean`, and `NeedleTwoStepOddSource.lean` against the unchanged original machine source. This supersedes earlier CI-pending notes for those **specific** odd-block and two-step files. Other source-mirrored files still need their own original-import audit. The two-step result specializes the prior Agent20 general inverse; its blanket-root relevance and external novelty are unproved. It does not decide Space Needle or BB(6).

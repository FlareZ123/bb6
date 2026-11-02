# Machine C exact arithmetic high-sector jumps (Agent 46, 2026-11-02)

**Status: verified formal intermediate reduction and finite computational evidence. Machine C and BB(6) are unresolved.** This directory contains source-level Lean proofs against the exact published Machine C accelerator as transcribed in Agent 11's `CLine.lean`, plus executable code and a reproducible trace.

## Certified all-time formulas

For every natural `a,k,c,n` with `n<=a` and `n+3<=c`, precisely `n` successful original `nextC` calls send `(a,k,c)` to `(a-n,k+n,c-n)`. Thus a high-sector run is batched in one arithmetic operation with length `min(a,c-3)`. The endpoint satisfies `a'=0` or `c'=3`; weighted rank `a+2k+c` is preserved across that descent.

`JumpHigh.lean` checks these claims without `sorry`. `JumpMacro.lean` defines a total step `macroNext` that executes the maximal batch when `a>0,c>=4` and performs one regular step otherwise, recording positive elapsed time `macroTime`. It establishes exact equality after that elapsed time for every input and the global biconditional:

```lean
(∃ n, BB6.Agent8Section.run BB6CLine.nextC n (some s) = none) ↔
(∃ m, BB6.Agent8Section.run BB6.Agent46.macroNext m (some s) = none)
```

`JumpSection.lean` additionally proves the all-natural affine return formula: when `k>=1` and `a>=2k`, exactly `2k+1` original accelerator steps take `(a,k,0)` to `(a-2k,2k+2,0)`.

**Source-level verification:** [manual CI 41426473436](https://github.com/FlareZ123/bb6/actions/runs/41426473436) compiled the unmodified upstream-in-repo `CLine.lean` and `GenericSection.lean`, then our exact batching and halting-equivalence proofs. [Manual CI 41427731624](https://github.com/FlareZ123/bb6/actions/runs/41427731624) also compiled `JumpSection.lean` against those same original sources. All successful Lean theorem axiom audits list only standard axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`. The original six-state TM-to-CLine bridge is separate upstream work, already verified by Agent 21 and cited in the cross-holdout decision-gates synthesis.

## Finite blank-origin experiment

The independent JS and C++ implementations were compared and agree at 200, 400, 600, 800 million and one billion zero-c section returns. The exact original initial `(5,0,1)` needs one step to reach `(5,1,0)`; the table counts that first step. A third original one-step interpreter and batched section simulator agreed on every pair `0<=a,k<128` (16,384 cases), including exact step counts. The numeric state coordinates in the reported experiment remain safely below JavaScript's maximum safe integer; the cumulative count is summed as `BigInt`.

| Zero-c returns | Section (a,k) | Original CLine steps |
|---:|---:|---:|
| 200,000,000 | (77,728,461, 661,107,198) | 69,989,047,325,718,469 |
| 400,000,000 | (517,029,556, 1,141,462,190) | 279,990,608,275,955,468 |
| 600,000,000 | (919,849,808, 1,640,104,096) | 630,021,888,602,053,022 |
| 800,000,000 | (138,014,520, 2,731,021,914) | 1,120,045,793,111,097,670 |
| 1,000,000,000 | (358,994,343, 3,320,495,488) | 1,750,010,467,923,799,866 |

No stop occurred within this finite prefix. This is **not an infinite-time nonhalting result** and does not improve the global BB(6) bound. Raw counter-accelerator steps are not equal to original TM individual steps.

Executable reproduction uses the portable CommonJS `jump-step.cjs` and `trace-jump.cjs`, with SHA256 over newline-delimited `sectionIndex,a,k,cumulativeSteps` sampled every 10,000 section returns. For the first ten million sections the SHA256 digest is `02c204fc14eadd31a2b325345870b18875aa430ecf6b894adf16cd470a4a247d`. Direct independent algorithms also checked exact counts for one billion sections; a complete formal certificate for that enormous finite trace is not claimed.

## Future research

Exploit the affine return branch and derive its other piecewise-affine cones to obtain a closed arithmetic two-counter return system. Use it to identify genuine all-time reachable-set invariants that exclude the infinite halting diagonal `(0,2j,4j+10)`, instead of merely lengthening finite traces.


## Additional symbolic return cones (source CI success)

[Manual CI 41429105149](https://github.com/FlareZ123/bb6/actions/runs/41429105149) compiled original CLine, generic section proofs, `JumpHigh`, `JumpMacro`, `JumpSection`, new `JumpBounce` and `JumpOneReturn` with every final axiom audit restricted to standard Lean axioms. The three new unconditional-over-each-region exact zero-c returns are:

| Input region, starting at (a,k,0) | Exact endpoint (a',k',0) | Number of CLine calls |
|---|---|---|
| a>=2, a even, a<2k<=3a+1 | (3a+1-2k, 2k-a+3) | 2k+2 |
| a>=3, a odd, a+3<=2k<=3a+3 | (3a+3-2k, 2k-a+2) | 2k-1 |
| k>=2, a=2k-1 | (4k-2, 3) | 2k |

The proof also gives all-natural `start_to_zero` for the initial high descent `(a,k,0) -> (0,a-1,2k-a+3)` in a-1 steps whenever 2<=a<=2k, and exact odd-/even-middle bounce-to-c3 formulas. These are actual exact returns. The property that these times are **minimal** first-return times has not yet been formalized. No complete return classification or blank-origin nonhalting argument has been established.

The number of CLine calls means only accelerator invocations. It must not be construed as the exact number of original six-state tape-machine steps. This is incremental structural research under `im-results/`, rather than a BB(6) frontier solution.


## Complete all-input arithmetic Machine C section, with formal blank-entry bridge

**Now CI-certified:** [run 41431197887](https://github.com/FlareZ123/bb6/actions/runs/41431197887) compiled original repository CLine, CReachBridge, CPhaseRank, GenericSection and CSectionTotal together with all new arithmetic source modules. The final `Agent46CBridge.lean` proves the exact biconditional `BB6.CReachBridge.RunHalts ↔ ∃ m, BB6.Agent8Section.run secNext m (some (5,1)) = none`. This connects the true blank-entry counter accelerator with an **executable, total, all-natural two-counter return map**.

The new arithmetic engine lives in:

- `JumpBounceSections.lean`: exact all-natural odd/even zero-left bounce continuation and return formulas. Odd middle `k` and high counter `c`: when `2k+6<c`, the arithmetic jump `(k,c) ↦ (2k+3,c-2k-3)` costs `2k+4` original CLine calls. When `4<=c<=2k+6`, it exits to `(2k+6-c,c,0)` after `c` calls. Even middle `k`: when `2k+8<c`, the jump `(k,c) ↦ (2k+4,c-2k-5)` costs `2k+3` calls. For `6<=c<=2k+8`, it exits to `(2k+8-c,c-1,0)` after `c-3` calls; `c=4` exits immediately, while `c=5` is the halting guard.
- `BounceCalc.lean`: structurally recursive, computationally executable `bounce k c`. Each recursive call strictly decreases `c`; parity stays fixed throughout continuing bounces, while `k` approximately doubles. This eliminates the previous linear high-sector scan.
- `BounceProof.lean`: Lean strong-induction proof `bounce_exact`, showing its computed elapsed CLine-call count and optional zero-c result are correct for **every** `k` and `c>=4`, including the genuine halting guard.
- `FastSectionDef.lean`: `exactSection`, `secTime`, `secNext` using closed-form low-counter cases and `bounce`. This is a completely total, arithmetic two-counter return interpreter.
- `FastSectionProof.lean`: unconditional `section_exact a k`, establishing the precise `secTime(a,k)` original CLine transitions reach `secNext(a,k)` embedded at `c=0` or halt.
- `FastSectionHalting.lean`: positive elapsed time and all-input `section_halts_iff` (infinite-time halting preservation).
- `Agent46CBridge.lean`: blank-entry `RunHalts` iff the arithmetic map `secNext` eventually returns `none` from `(5,1)`. All composed against original shared source with successful CI.

The old Agent8 total computable section map had a provable `O(k)` bounded scan per return. The new implementation uses a logarithmic-length chain of explicit arithmetic bounce updates in the high-counter branches; each continuation grows the middle counter by at least a factor approaching two. No general global nonhalting conclusion follows from this speedup. The exact BB(6) value remains unresolved.

**Caution:** `RunHalts` here is the formally proved stopping property of the published accelerated Machine C encoding connected through the existing Agent21 bridge. It is not a new universal six-state Busy Beaver upper bound.

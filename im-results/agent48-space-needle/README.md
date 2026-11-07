# Space Needle: original-source arithmetic, complete inverse, and blank-root boundary

**Research status, 7 November 2026.** The Space Needle machine `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD` remains undecided from its true blank root. The strongest reusable results here are a complete source-connected high-level transition classification, source-certified fifth-linear terminal inverse enumeration, and an original-root argument excluding the two exceptional fifth-bound feeders. The **fifth-linear arithmetic and complete terminal-list theorems passed original-source [CI 42332720650](https://github.com/FlareZ123/bb6/actions/runs/42332720650)** with only standard axioms and no `sorryAx`. The separate blank-root exclusion and integrated fifth-linear halting equivalence have been submitted to [source CI 42333153807](https://github.com/FlareZ123/bb6/actions/runs/42333153807) and remain **pending verification** until that run completes. Neither the original machine nor BB(6) has a halt/nonhalt decision, a new attainable Busy Beaver score, or a global maximum proof.

## Original-source semantics and decisive unknown

The source is the published [Google DeepMind Cryptids Space Needle module](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean), revision `ced8f9f44f67a167d5ecc03e687b048c67926371`, whose theorem reduces original blank-tape halting to iterating `highLevelNext` from `N 1`. [SpaceNeedleClosed.lean](SpaceNeedleClosed.lean) gives the exhaustive source transition:

```text
H(0)=0; H(k+1)=2(H(k)+1); H(k)+2=2^(k+1)
O(q,0)=2q+1; O(q,k+1)=2(O(q,k)+1); O(q,k)+2=2^k(2q+3)
scanEven(H(k),b)=none
scanEven(O(q,k),b)=some(N(b+O(q,k)+k+3(q+1)))
```

For a nonterminal counter `d`, write `d+2=2^v(2q+3)`. Its successor is `d'=d+v+3(q+1)`, and every successful call strictly increases `d`. Terminal counters are `d=2^K-2`, `K>=1`. A source `O(q,v)` is an immediate terminal predecessor **iff**

```text
2^K=(2^(v+1)+3)q+3*2^v+v+3.
```

The unsettled all-time question is whether any `2^K-2` occurs on the deterministic orbit starting `d=1`. [SpaceNeedleRawBridge.lean](SpaceNeedleRawBridge.lean) and [Agent 20's root decision](../agent20-needle-coprime/NeedleRootDecisionSource.lean) formalize the raw-machine halting criterion and exact reachability of each **fixed** counter. Neither closes the unbounded existential in K.

## Strongest theorem-level reductions

| Mechanism | Scope and evidence | Missing root-level conclusion |
| --- | --- | --- |
| **Fifth-linear terminal inverse** | [FIFTH-BOUND.md](FIFTH-BOUND.md), [FifthHigh.lean](FifthHigh.lean), [NeedleQuinticEnumerate.lean](NeedleQuinticEnumerate.lean) and [source bridge](NeedleQuinticEnumerateSource.lean). Every terminal predecessor satisfies `5v<=K+3` or is one of the two exact triples `(61,6,13)`, `(340282366920822406584691642613415018481,42,171)`. The finite list tests `v<=floor((K+3)/5)` plus exceptions; membership is iff for **all K**. Original-source **CI 42332720650 passed**, auditing only standard axioms. | Which regular feeder, if any, actually occurs from blank? |
| **True-root exceptional exclusion** | [SpaceNeedleFifthRoot.lean](SpaceNeedleFifthRoot.lean) computes the complete immediate predecessor list of the 171-bit `v=42` exceptional source as empty, and uses authentic original-root semantics to exclude its reachability. Agent 20 [already source-certified](../agent20-needle-coprime/NeedleRootSharp.lean) nonreachability of the `v=6` exception. Integration gives `IsHalt target` iff some **reachable** listed feeder satisfies `5v<=K+3`. **Original source CI 42333153807 pending.** | An unbounded all-time regular-feeder exclusion or genuine hit. |
| **Automatic all-slope inverse** | [SuperlinearOne.lean](SuperlinearOne.lean), [SuperlinearOptimized.lean](SuperlinearOptimized.lean) and [source proof](SuperlinearOptimizedSource.lean) sharpen candidate cutoffs when `v>=3^c+1` and choose a slope among logarithmically many candidates. Source CI [42301784364](https://github.com/FlareZ123/bb6/actions/runs/42301784364) passed. For sufficiently large K this can be tighter than the uniform fifth-linear bound. | Reverse candidate restriction alone does not decide reachable feeders. |
| **Earlier quartic, sharp and boundary classifications** | [QUARTIC-ENUMERATION.md](QUARTIC-ENUMERATION.md), [OFFSET-STRIP.md](OFFSET-STRIP.md), [BOUNDARY-EXACT.md](BOUNDARY-EXACT.md). The earlier quartic list tests through `floor((K+2)/4)`; boundary equality `K=3v+3` has only `(45,2,9)`, `(214,3,12)`. Source CIs [42296731159](https://github.com/FlareZ123/bb6/actions/runs/42296731159) and [42298248203](https://github.com/FlareZ123/bb6/actions/runs/42298248203) succeeded. | Exact source list is conditional on target and does not bound all K. |
| **Odd-block acceleration and two-step terminal inverse** | [ODD-BLOCKS.md](ODD-BLOCKS.md), [ORDER-5ADIC.md](ORDER-5ADIC.md), [TWO-STEP-ODD.md](TWO-STEP-ODD.md). Odd-block lengths feeding an exact terminal exponent K satisfy the iff `4*5^(t-1) | K`. Two-step odd terminal equation is source-certified in CI [41931806607](https://github.com/FlareZ123/bb6/actions/runs/41931806607); complete odd lengths in [41935571573](https://github.com/FlareZ123/bb6/actions/runs/41935571573). | Synthetic odd blocks may have no authentic blank history. |
| **Unrestricted terminal source density and fan-in** | [TERMINAL-RESIDUES.md](TERMINAL-RESIDUES.md) covers every decimal residue of incoming exponents. [FIVE-TERMINAL.md](FIVE-TERMINAL.md) gives five simultaneous synthetic source valuations `0,3,20,38,83`, extending Agent 20's three-source theorem ([CI 42107688083](https://github.com/FlareZ123/bb6/actions/runs/42107688083)). Five sources are original-source certified by [CI 42296731159](https://github.com/FlareZ123/bb6/actions/runs/42296731159). Agent 20 also gives an unrestricted unbounded-indegree [paper construction](../agent20-needle-coprime/UnboundedFanin.md) for nonterminal destinations. | Incoming degree has no implication for a unique deterministic blank orbit. |

The new 171-bit exceptional predecessor is an instance of [Agent 20's earlier unbounded-valuation synthetic construction](../agent20-needle-coprime/NeedleVariableValuation.lean); that construction is credited and retained. The substantive additional question answered here is its finite incoming-source/blank-root nonreachability, pending original-source CI. None of the statements has been promoted as a standalone externally novel mathematical publication.

## Finite diagnostics and next mathematical obligation

An earlier exact-integer forward experiment from `N 1` checked 30,000 successful calls and reached 28,098 bits without encountering a power-of-two input. Another 300,000-call finite test visited all residues of `d+2` modulo `2^14`, refuting simple fixed small-modulus single-state invariant proposals. These computations establish only their finite observations.

The [fifth-bound proof and source-root certificate](FIFTH-BOUND.md) are intended as tools for **history-sensitive actual-root analysis**. To advance BB(6), the next useful theorem must eliminate every remaining authentic terminal feeder or produce a genuine terminal witness, with a proof transporting to the raw machine. Further synthetic density studies or finite traces alone do not address that quantifier. The [manual-only original-source workflow](../../.github/workflows/agent48-space-needle-five.yml) has no per-push trigger and preserves a pinned upstream revision.

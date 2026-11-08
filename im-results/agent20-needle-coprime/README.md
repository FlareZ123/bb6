# Space Needle: exact source inverse and blank-root decision interface

**Research state:** The original six-state Space Needle machine and BB(6) remain undecided. This dossier establishes an exact per-target blank-root decision procedure, sharp terminal valuation restrictions, genuine-root exclusions for individual feeders, and constructive infinite families of legal *synthetic* predecessors. Full derivations and older provenance are retained in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).

## Original machine and complete per-target decision

Machine: `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`. Pinned Cryptids source: `google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371`, originally blank-entering at `N 1`. In Agent 48's [source proof](../agent48-space-needle/SpaceNeedleClosed.lean), every successful high-level step has `d+2=2^v(2q+3)`, and successor `d'=d+v+3(q+1)`. Terminal inputs have `d=2^K-2`, `K≥1`. The source equation for a legal immediate terminal feeder is:

```text
2^K = (2^(v+1)+3)q + 3*2^v + v+3
source = 2^v*(2q+3)-2
```

[NeedleGeneralInverse.lean](NeedleGeneralInverse.lean) and its [source bridge](NeedleGeneralInverseSource.lean) enumerate every incoming state of any target with at most `floor(log2(e+2))+1` parameter trials. [Source CI 41883568806](https://github.com/FlareZ123/bb6/actions/runs/41883568806) passed.

[NeedleRootDecisionSource.lean](NeedleRootDecisionSource.lean) proves `reverseCheck finiteParents (d+1) d = true ↔ ReachN d` for *every fixed* target `d` in the **original blank-start orbit**. It further proves equivalence of original raw-machine halting with an *unbounded existential* over the exact terminal root tests. [Original source CI 42212170672](https://github.com/FlareZ123/bb6/actions/runs/42212170672) passed both jobs and audited only standard Lean axioms, no sorry. This settles each individually supplied target's reachability without deciding the global terminal existential.

[NeedleSharper.lean](NeedleSharper.lean) and [source](NeedleSharperSource.lean) prove `3v+3≤K` for every direct terminal feeder, except the unique synthetic triple `(q,v,K)=(61,6,13)`. The [original-source rooted theorem](NeedleRootSharp.lean) excludes its source counter 7998 from the genuine blank orbit using 12 exact initial returns and strict growth. Hence `raw_halts_iff_reaches_sharp_feeder` has **no exceptional reachable feeder**. Both final theorem audits passed [source CI 42212170672](https://github.com/FlareZ123/bb6/actions/runs/42212170672).

## Constructive synthetic terminal ancestors

[NeedleThreeTerminalParents.lean](NeedleThreeTerminalParents.lean) and [source adapter](NeedleThreeTerminalSource.lean) prove every `K=1756236+1855188t` has at least **three distinct** incoming source states, with valuations 0, 3 and 20. Complete unchanged-source [CI 42107688083](https://github.com/FlareZ123/bb6/actions/runs/42107688083) succeeded. See [TerminalTriple.md](TerminalTriple.md).

New [NeedleVariableValuation.lean](NeedleVariableValuation.lean) proves for every `t≥0` an exact incoming terminal source with **`v>t`**, `2v=9^(t+1)+3`, `K+1=2(t+1)(v+1)`. Examples: `(v,K)=(6,13),(42,171),(366,2201)`. The proof is **locally Lean 4.36.0-rc2 kernel checked**, with only `[propext, Quot.sound]` and no sorry. The [source adapter](NeedleVariableValuationSource.lean) is being checked in a separate [manual source workflow](../../.github/workflows/agent20-needle-triple.yml). Read [VariableValuation.md](VariableValuation.md) for the constructive geometric identity and provenance; do not infer blank-orbit reachability from these edges.

The independent [unbounded synthetic fan-in construction](UnboundedFanin.md) remains a paper argument using CRT and Euler's theorem, with one [ten-parent Lean instance](NeedleTenParentWitness.lean). A collection of [modular source family results](SpaceNeedleMod30.lean), [odd-modulus saturation](SpaceNeedleOdd.lean), and [coprime-15 saturation](SpaceNeedleDensity.lean) are locally kernel-checked. Their scope is unrestricted legal predecessors, and their external novelty is unreviewed.

## Cancellation feeder arithmetic and rooted exclusions

The exact cancellation family has (v=(9^r+3)/2) and (K+1=r(9^r+5)). Existing original-source Lean work excludes the first four individual cancellation feeder sources from the genuine blank orbit. Agent 48's [r=5 no-parent audit](../agent48-space-needle/R5-CANCELLATION-ROOT-AUDIT.md) is exact-integer computational evidence pending a finite Lean certificate.

An independent [all-parameter high-valuation strip theorem](CancellationTopStrip.md) now excludes the top `(9^r+1)/2` candidate parent valuations for **every** positive cancellation parameter `r`. Its [standalone Lean proof](CancellationTopStrip.lean) is locally kernel-checked with only standard axioms and an exact source-equation form. This is an infinite predecessor exclusion, with every lower valuation and actual blank-root outcome still open for general `r`.

A complementary [uniform modulo-five theorem](CancellationTopStrip.md#complementary-all-parameter-modulus-five-obstruction) excludes the four inverse valuation classes `u mod20 ∈ {0,8,12,16}` for **every** cancellation parameter `r≥1` throughout the full physical valuation range. Independent [Lean proof](CancellationMod5.lean) and [source-equation adapter](CancellationMod5SourceEq.lean) have been locally kernel checked. The [constructive odd-part proof](CancellationTopConstructive.lean) and [exact terminal equation](CancellationTerminalConstructive.lean) derive each cancellation feeder directly, rather than assuming it exists. The [pinned-source high-level adapter](CancellationOriginalBridge.lean) is under original-upstream CI review; until that run passes, it is a source bridge candidate.

The new [r=6 no-parent audit](R6Cancellation.md) independently exhausts all 3,188,676 potential predecessor valuations of the sixth cancellation feeder: 2,579,052 excluded by small-prime witnesses, 50,877 checked by a GMP modular polynomial method, and 558,747 checked by exact signed-base remainders. Both surviving intervals have zero incoming parents. This is a **complete computational exclusion of that one genuine-root feeder**, conditional on the previously source-certified exact inverse correspondence, with the full finite check not yet kernel-certified. The [uniform polynomial identity](CancellationSparsePolynomial.lean) is independently kernel-checked in Lean 4.36.0-rc2 and is useful for faster arithmetic certificates. Its two independent executable audits are [low C++](r6_low_polynomial.cpp) and [high Python](r6_high_parent_audit.py). These exclusions do not bound the unbounded remaining terminal exponent.

## Open decisive question

No theorem here says any terminal feeder is reached by the genuine blank-start sequence. The exact Boolean root test is sound and complete **only for each fixed target**; the existential over all terminal powers remains open. Source-level inverse classification, arbitrary synthetic indegree and infinite modular coverage cannot alone establish nonhalting. A useful breakthrough must exclude a whole surviving infinite family from the authentic orbit, or produce a genuine terminal witness, then ultimately connect every remaining six-state machine and exact champion score to global BB(6) coverage.

See [Agent 48's exact odd-block grammar](../agent48-space-needle/ORDER-5ADIC.md) for potential authenticated-root strengthening. This dossier belongs in `im-results/`; nothing established here certifies a BB(6) upper bound or a standalone novel publication.

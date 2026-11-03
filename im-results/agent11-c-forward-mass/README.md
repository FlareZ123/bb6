# Machine C: finite forward mass-crossing certificate for low halting parameter m=8

**Agent 11, 2026-11-03. Intermediate original-source-bridge candidate, not a BB(6) decision.** Pilot [R-20261103T1305Z-agent11-c-forward-mass](../../research/issues/R-20261103T1305Z-agent11-c-forward-mass.md). This contribution is mathematically distinct from Agent1/Agent34's 41-node backward-cone attempt: a **finite forward proof** combined with an **all-time strict mass bound**.

## Precise theorem and mathematical proof

The source Machine C section map `BB6.Agent46.secNext` starts at `(5,1)`; its low halting parameter `m=8` is `(1,K_8)=(1,524260)`, satisfying `K_8+3*8+4=2^(2*8+3)`. Let `W(a,k)=a+2k`. The exact source proof [SectionMassStrict.lean](../agent3-c-bounce-inverse/SectionMassStrict.lean) establishes **for every** successful section edge `s→t` that `W(s)+2≤W(t)`. A reproduced, locally kernel-checked arithmetic section map has the following consecutive blank-origin return states:

| Return index | State | Weight |
|---|---|---:|
| 150051 | (104382, 472065) | 1048512 |
| 150052 | (621619, 213453) | 1048525 |
| low halt m=8 | (1, 524260) | 1048521 |

Thus if the authentic source orbit follows the certified forward prefix, it cannot hit the m=8 target: any earlier occurrence would contradict strict growth from the earlier target to the lower-weight index-150051 state; any later occurrence contradicts strict growth from the higher-weight index-150052 state. This is an **all-time** exclusion of one exact genuine low-halting input, conditional only on the exact source-bridge completion.

## Locally kernel-checked construction

`Core.lean`: exact arithmetic section result map `CForward.next` transcribed from the Option component of original [BounceCalc.lean](../agent46-c-jump/BounceCalc.lean) and [FastSectionDef.lean](../agent46-c-jump/FastSectionDef.lean). Defines `walk` and proves for arbitrary `n` and input states the `walk_mass_lower` and `not_reached_by_crossing` theorems.

`Mass.lean`: independently proves for **all** successful edges of this transcribed map the strict inequality `a+2*k+2≤x+2*y`, including exceptional and recursive bounce branches. This is a local copy-semantic version of Agent3's already existing source-verified mass theorem.

`TracePart0.lean` through `TracePart7.lean`: 37 separate `decide +kernel` chunks (36 of length 4096 and one of length 2595), composed by pure Lean `walk_add`; formal exact endpoint
```lean
CForward.walk 150051 (some (5,1)) = some (104382,472065)
```
All eight modules compiled successively under original uploaded Lean **4.36.0-rc2**. No `sorry`, custom axioms, `native_decide`, or external solver results enter the certificate.

`MassCross.lean` gives the abstract crossing contradiction. `Final.lean` proves **unconditionally for the transcribed map**:
```lean
CForward.copied_m8_nonreach :
  ¬ ∃ n, CForward.walk n (some (5,1)) = some (1,524260)
```
Local `#print axioms` emitted exactly `[propext, Quot.sound]`. All source proof files compiled locally; this is a Lean kernel theorem for the copied section definition.

`Reference.lean` reproduces literally the **result-relevant source definitions** of original Agent46's time-aware `bounce`, `exactSection`, `secNext`, replacing only transitive imports. `SourceBridgeTest.lean` proves in local Lean
```lean
CForward.bounce k c = (BB6.Agent46.bounce k c).2
CForward.next p = BB6.Agent46.secNext p
CForward.source_m8_nonreach :
  ¬ ∃ n, CForward.sourceWalk n (some (5,1)) = some (1,524260)
```
Axiom audit for each bridge theorem: `[propext, Quot.sound]`. The proof spans **all** natural parameters, not sampled trace states. `SourceBridgeOriginal.lean` replaces the test import of `Reference` with the actual original `FastSectionDef`. **Its build against the entire genuine imported source chain remains pending.** The two imported source definitions were inspected and matched literally, but this standalone check must not be described as an original-source-CI certificate.

## Reproduction and provenance

The compressed source archive `proof-src.tar.xz.b64` contains all 17 compact scripts/modules and an exact SHA256 checksum recorded in the next revision. Reconstruction uses the standard library and should verify SHA256 before unpacking. Compile in the following order (each import relies on the previous `.olean`):

```text
Core, Mass, TracePart0, TracePart1, TracePart2, TracePart3,
TracePart4, TracePart5, TracePart6, TracePart7, MassCross, Final,
Reference, SourceBridgeTest
```

The independent deterministic Python section interpreter constructed all 150052 states and generated chunk endpoints; its raw state-chain SHA256, over UTF-8 concatenation of `"a,k;"` for indices 0 through 150051 inclusive, is `8016ba1728d7be9ffa0534315327e4b19d1fa89b5b9b2d222fd65293e0dfa9b9`. Both the 150052nd step and the crossing weight were checked independently from the Lean evaluation.

**Verification boundary:** Before promoting this as a genuine original-source rooted target exclusion, compile `SourceBridgeOriginal.lean` against the unchanged authentic modules and audit axioms. Hosted GitHub Actions manual jobs were failing before any job step as of 2026-11-03 12:50 UTC, so no further dispatch was performed during this incident. The original published DeepMind TM-to-section bridge also remains a dependency for interpreting source-section nonreachability as raw blank-machine gate exclusion. Even after source-checking, this proves only one halting parameter inaccessible, with infinitely many other parameters unresolved. No BB(6) exact value or improved global upper bound is claimed.

## Next

After CI restoration, compile the already prepared source bridge in the existing manual workflow (no per-commit workflow). Obtain independent review of the exact source-to-section semantics and use the method to certify other halting targets if the crossing can be found without giant traces. The proof-compression mechanism is reusable; a single exclusion remains intermediate research.

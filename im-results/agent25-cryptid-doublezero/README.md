# Agent 25: Cryptid D-start exact conditional returns

All source modules in this directory are **intermediate**, with no claim of deciding the original blank-tape machine or BB(6).

Machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, states A=0 through F=5. `DoubleZero.lean` defines the twelve original raw transitions on a two-sided finite-list tape with implicit zero extension.

**New universal theorem:** `TripleUniversal.lean`, built from `TripleUniversalBase.lean`, `TripleUniversalCore.lean`, and `TripleUniversalWalk.lean`, proves the unbounded suffix-parametric return
```
run (6*m+41) (ab m ([1,1,1] ++ ys)) = ab (m+4) ys
```
for every natural m and arbitrary finite Boolean suffix ys. Here `ab m xs` is state A scanning zero, left stack `0 (10)^m 11`, and right stack xs. `TripleIteration.lean` proves for all m,q,ys:
```
run (12*q*q+(6*m+29)*q) (ab m (1^(3q) ++ ys)) = ab (m+4*q) ys
```
The block `1^(3q)` is implemented as `tblock q` by recursion. The formula holds at arbitrarily large q and does not require assumptions on the suffix. Both theorem checks report only standard axioms `[propext, Quot.sound]` with Lean 4.36.0-rc2 and no sorry. The proof is about raw steps, not an extrapolation from experiments.

`TripleUniversal.lean` is stored in losslessly compressed `TripleUniversal.lean.xz.b64`; reconstruct with `python unpack.py`. Expected decoded SHA-256: `630ac7599e52b2daefb768e4f514e5375b9ce17b415971244f10d043a4d1a4c6`. Verify in dependency order: DoubleZero, TripleUniversalBase, TripleUniversalCore, TripleUniversalWalk, TripleUniversal, TripleIteration. A separate `DoubleZeroE.lean` derives a conditional E return with an internal zero and six ones.

Together with Agent 31's already-checked `prefix_A` theorem, the iteration formula yields a conditional F-section macro for `I_(3k+3)(0 1^(3q) 0 ys)`, with new unary length `8k+8q+11` after `12k²+49k+44+12q²+(24k+55)q` raw steps. **Composition across independently defined configurations is a pending formal bridge**. An independent raw blank-tape simulation verified the resulting `I_27659([])` at 166,999,736 steps, following the mixed-suffix `I_10365(0 1^6)` at 23,503,104 steps. Finite checks do not establish nonhalting.

See also Agent 31's `im-results/agent31-cryptid-boundary/README.md`; Agent 26 is investigating a disjoint E-branch.

## 21:20 UTC: authentic blank-origin continuation through 360 sextillion

This reincarnation of Agent25 produced an **original-source Lean 4.36.0-rc2 certificate** that extends the genuine D-start blank execution past the previous 19,848,692,333,528,818,046-step verified checkpoint. See [BlankNext.lean](BlankNext.lean), [BlankCodeImplicit.lean](BlankCodeImplicit.lean) and [successful full-source manual CI 41527274374](https://github.com/FlareZ123/bb6/actions/runs/41527274374). Every newly printed theorem's axiom audit is exactly `[propext, Quot.sound]`, with no `sorryAx`.

| Original blank-tape primitive step | Physically verified F-on-0 section |
| ---: | --- |
| 141,146,256,421,739,780,247 | `I_25434628786 ((01)^3 0 1^4)` |
| 1,003,706,711,874,695,788,461 | `I_67825676761 ((01)^6)` |
| 7,137,469,949,709,248,558,298 | `I_180868471357 (0 1^18)` |
| 50,755,341,858,758,075,791,267 | `I_482315923617 ((01)^2 0 1^15)` |
| **360,926,875,448,096,383,250,204** | **`I_1286175796359 (empty)`** |

The third return exercises Agent32's original-source `full_E_pairs_implicit_blank`; `ObsEq` plus a proved physical padding step handles the one missing trailing zero. The fourth uses the original `full_E_triple_pairs`. The fifth applies an **independent alternate physical-tape derivation** `BB6.Agent25.full_A_code_implicit_blank`, for all `k : Nat` and finite coded words `ws : List Bool`. Agent32's **earlier** `BB6.Agent32Code.full_A_code_implicit_nil` in `im-results/agent32-cryptid-padding/CodeImplicitNil.lean` already proves the **stronger exact equality** at this same implicit-blank input. Our physical variant composes Agent35's exact original-machine `full_A_code` with Agent32's padding bisimulation. **Do not claim this universal macro as mathematically novel.**

This rigorously promotes Agent32's previously *conditional* projected `I_482315923617` and `I_1286175796359` sections to actual blank-start theorems. It is **finite, intermediate progress**, and remains far below known BB(6) champion lower bounds. Neither this machine's halting problem nor BB(6) is decided. Do not migrate this document to `results/`.

The [reused manual workflow](../../.github/workflows/agent35-blank-beyond.yml) restores SHA-pinned original sources, compiles the complete unmodified chain, checks both new modules, and prints axioms. No per-commit trigger was added. Continued frontier work should seek a forward-closed reachable-suffix invariant, authenticated original-source halting witness, or a scalable kernel certificate for genuinely large sequences of symbolic returns.

## 2026-11-03: authentic 8394-return blank-root exception rejoins regular D language

**Original-source Lean 4.36.0-rc2 certification: [two-checkpoint CI 41716055765](https://github.com/FlareZ123/bb6/actions/runs/41716055765), [true blank-root CI 41716508754](https://github.com/FlareZ123/bb6/actions/runs/41716508754).** All final theorem audits contain only standard axioms, no `sorryAx`: the conditional theorem has `[propext, Quot.sound]`; the true-blank theorem has `[propext, Classical.choice, Quot.sound]`.

Agent2's authentic [8394-return certificate](../agent2-cryptid-continuity/BlankRegular8394.lean) reaches, from the real empty tape after an exact symbolic raw duration `T=36+DRegular.accumulated 8394 seed9`, a section `I_a((01)^6 1)` where **a=9t+4** for an actual (very large) natural t. The exact congruence, including q=6 and b=1, is checked by Lean evaluation of the previously source-authenticated regular model in `BlankRootRejoin.lean`.

The source-certified E double macro of Agent32 followed by the genuine original-source B rule supplies the universally quantified **two-endpoint** source identity

```text
I_(9t+4)((01)^6 1)
  --[ E cost 12(3t)^2+49(3t)+80 ]-->
I_(24t+5)(0 1^12 0 1^6)
  --[ B cost 12(8t+1)^2+49(8t+1)+40 ]-->
I_(64t+29)(0 1^6)
= L(64t+29,1,5).
```

The theorem `BB6.Agent25Rejoin.exceptional_EB_two_source`, in [ExceptionalBRejoin.lean](ExceptionalBRejoin.lean), holds **for every t** with physical `BoundaryPadding.ObsEq`. The physical input has **implicit** right-hand zeros, and the proof applies `Agent32EAll.all_e_double_implicit_blank` directly rather than incorrectly equating finite word `...11` with `...1100`. Source `full_B` then gives an **exact** second step `exceptional_B_rejoins_regular`.

[BlankRootRejoin.lean](BlankRootRejoin.lean) imports the unchanged `BlankRegular8394.blank8394` and composes it with the two source steps. Its theorem `BB6.Agent25RootRejoin.blank_two_more_returns` proves an original **blank-origin** physical return to `L(64t+29,1,5)` at the explicitly quantified total raw time `T + Ecost + Bcost`. The original 8394-step regular model had deliberately returned `None` at this E exception. The machine has now been certified through that language exit and into its regular family again. These are specified physically correct F/0 checkpoints; universal absence of intermediate F/0 sections is not claimed.

**Prior art and scope.** Agent31's [nine-case second-return classification](../agent31-d-exceptional/two-return-classification.md) already derived this k≡0(mod3) E/B return formula from earlier source macros, so the conditional algebra has **no originality claim**. The new contribution is direct all-parameter Lean `ObsEq` composition and transport to a **true blank-tape** witness of the source-certified 8394th section. This is still a finite D-machine computation, no exact BB(6), no full nonhalting proof, no champion bound. Retain under `im-results/`.

**Next research obstacle:** exploit this physical reentry to transport the subsequent regular model interval and isolate the next true-root off-language packet (the model predicts around index 31,787, not yet source-certified here); then find a genuinely closed orbit language or halting obstruction. Do not interpret finite source composition as global nonhalting.

# Root-specific terminal exclusions for BB(6) holdout #429, six new residue classes

Agent 30, 2026-11-04. **Intermediate original-blank-root mathematical progress; BB(6) and holdout #429 remain undecided.** These are unbounded-time inverse-chain certificates for the actual accelerated blank orbit, with genuine implications for a particular six-state machine. External research novelty has not been independently assessed. Keep in `im-results/` pending scholarly significance review.

## Exact problem and new results

The rooted machine `1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA` has the twelve-branch exact `BB429.next` and partial `BB429.run` in the **unchanged** [Agent5 BB429Rank](../agent5-429-rank/BB429Rank.lean). Its genuine accelerated entry is `(0,0)`. A successful state `(a,b)` lies on its unique halting line precisely when `b+1=2*a` (by `next_none_iff_halt_line`). Four separate all-natural Lean theorems prove, for **every** `n,a,b : Nat`,

```lean
BB429.run n (0,0) = some (a,b) →
    b+1=2*a →
    a%512≠393 ∧ a%512≠265 ∧ a%1024≠137 ∧ a%1024≠521
```

as the conjunction of the named individual lemmas `blank_halt_not_393_mod512`, `blank_halt_not_265_mod512`, `blank_halt_not_137_mod1024` and `blank_halt_not_521_mod1024` in their respective `BB429No...lean` modules. These exclude the **six distinct** terminal first-counter residues

```
a % 1024 ∈ {137, 265, 393, 521, 777, 905}
```

from the actual blank-root orbit, uniformly for every positive quotient of the modulus. They are disjoint from Agent6 and Agent18's earlier `a%1024∈{125,253,381,509}` exclusions, all of which reside in the different 125(mod128) sector. **No halting witness or universal nonhalting theorem follows.**

The earlier original-source [44-class halting iff](../agent6-harmonic429/SourceRawHalt44.lean) permitted these six classes. Composing both reductions gives an **exact raw-machine halting iff** with **38 of 1024** potential terminal first-counter residues, witnessed in `SourceRawHalt38.lean` as `BB429ActualHalt38.raw_halts_iff_38_gates`. The intermediate `SourceRawHalt42.lean` and `SourceRawHalt40.lean` successively add the `393` and `265` exclusions. The exact 38/1024 count is a simple pairwise-disjoint residue-set count, **not a percentage of undecided Turing machines, probability of eventual halt or estimate of closeness to BB(6)**. For the previously surviving 9(mod128) terminal sector, the only possible residues at modulus1024 are **9 and 649**. The other 36 permitted 1024 residues lie in the earlier 53,73,81,117,125(mod128) sectors. Every permitted class remains only a necessary possibility.

## Source-rooted proof mechanism

These proofs invert the unchanged twelve-branch `BB429.next` exactly, using exhaustive Lean case splits, arithmetic `omega`, and the previously source-checked invariant:

```
BB429.run n (0,0)=some (u,w), 0<u, u%2=0  =>  w%4=2.
```

The initial halting line `(a,2a-1)` for `a=128q+9` has a forced first-branch parent `(64q+3,384q+26)`, and source-exact parity forces further ancestors through successive first / nonfirst branches. All four certified classes eventually require a blank-reachable **positive even first counter with second counter differing from 2(mod4)**, which contradicts the invariant. Every alternative `next` predecessor branch is either explicitly impossible or propagated into a further forced ancestor and discharged.

The common backward spine has the exact affine expressions (later to earlier):

```
(128q+9, 256q+17)
(64q+3, 384q+26)
(160q+3, 192q+15)
(80q, 352q+18)
(168q+1, 176q+9)
(84q-1, 344q+10)
(170q-5, 172q+7)
(85q-4, 342q+2)
```

The last branches distinguish q modulo4/8. The preceding display is an orientation aid; actual Lean lemmas check each branch exhaustively and handle natural-number boundary conditions separately. In particular the `q=0` case is excluded already by the source-root `u=5` impossibility. There are no fixed-depth simulation assumptions in the proof.

## Formal evidence and reproduction

The four theorem sources are immutable SHA256-checked compressed `.lean.xz.b64` files. The atomic exclusive-lock [unpacker](./unpack.py) reconstructs `BB429No{393mod512,265mod512,137mod1024,521mod1024}.lean`:

| Theorem source | Original Lean SHA256 |
| --- | --- |
| [393 mod512](./BB429No393mod512.lean.xz.b64) | `205eb810e98022eb2641dcd8ebce07fedc564064dc00dfec01faca0c68fa280e` |
| [265 mod512](./BB429No265mod512.lean.xz.b64) | `ea2cac2c571fcc26f25f32bf37d025ae55dd85f404afb4395913422c1d9bbe3a` |
| [137 mod1024](./BB429No137mod1024.lean.xz.b64) | `e5b007e4372467d9f7d9f2d72e064b70bf551ee4b7bc23d9fae796fc9cdbd3d8` |
| [521 mod1024](./BB429No521mod1024.lean.xz.b64) | `d306d4e562d64e96777cd13b32c1ae767783b09f0783d667bb9283657f8e2e59` |

The [manual local-source proof workflow](../../.github/workflows/agent30-429-393.yml) compiles untouched Agent5/Agent6 dependencies and all four certificates with Lean 4.36.0-rc2. Successful verification runs:
* [41874779432](https://github.com/FlareZ123/bb6/actions/runs/41874779432) establishes `393`;
* [41875816846](https://github.com/FlareZ123/bb6/actions/runs/41875816846) adds `265`;
* [41876754446](https://github.com/FlareZ123/bb6/actions/runs/41876754446) checks **all four** together.

All verified assertions are kernel checked with ordinary foundational Lean axioms only; no `sorry` or `native_decide`. The plain Lean modules require their published dependency `.olean` files, so execute the workflow or compile dependencies in its pinned order.

The full [manual native source bridge workflow](../../.github/workflows/agent30-429-393-native.yml) additionally builds **unchanged Google DeepMind Cryptids high-level and raw-TM formalization** at commit `c86f15861709b76042998c5211c7b2f83991621b` using its pinned Lean 4.35.0-rc4, then verifies the original raw `IsHalt target` criterion. The earlier **42-class** original-source proof succeeded in [run 41875066255](https://github.com/FlareZ123/bb6/actions/runs/41875066255). The complete **38-class** original-source chain passed in [run 41878382504](https://github.com/FlareZ123/bb6/actions/runs/41878382504), at commit `1fb5b773cce77f1f61a0ac5f82efaf61ca774a8a`: both the pinned upstream accelerator build and the final `SourceRawHalt38.lean` compilation succeeded. The previous [run 41876912416](https://github.com/FlareZ123/bb6/actions/runs/41876912416) failed during oversized Mathlib cache extraction; the successful run used dependency-scoped cache retrieval. This source certification proves the 38-class **necessary gateway equivalence**, not a blank-root halt/nonhalt decision.

## Limitations and next discriminating problem

This is a root-specific all-time restriction, stronger for this single holdout than synthetic inverse feasibility. It does **not** prove the original root halts or runs forever, and it cannot imply an upper bound for all six-state machines. Other #429 researchers may discover overlapping proofs; preserve internal novelty credit by checking the current Agent6/18 dossiers and communications.

The remaining `9` and `649` modulo1024 sectors are not excluded. Small finite reverse-tree experiments find fast contradictions for many fixed numerical targets, but no parameter-uniform proof is yet available for those two complete sectors. An all-parameter inverse-rank, automaton, or forward blank-orbit invariant resolving either entire sector is more consequential than extending a fixed modulus routinely. The separate previously surviving `125` sector likewise remains open. A full nonhalting decision would need to exclude every possible terminal state or provide a genuine halting trace.

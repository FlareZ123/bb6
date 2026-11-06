# Cryptid #623: exact infinite four-predecessor collisions and ninefold transfer

**Agent 8, 2026-11-03. Status: original-source authenticated.** Standalone accelerated arithmetic was compiled with Lean 4.36.0-rc2; the unchanged Google DeepMind Cryptids module and the direct-import proofs were compiled by pinned Lean 4.35.0-rc4 in [successful manual CI 41676854489](https://github.com/FlareZ123/bb6/actions/runs/41676854489), job `126059699001`, whose source-theorem step 10 passed at 16:47:13 UTC. The checked `TernaryInverseSource.lean` has blob SHA `af2f3bd9ea7b656226ca5dc6a4ddff69bc064a5c` both at the CI head `2afdbf97e27f0e4ccf84c7d99a001df70ae7f91c` and at the subsequent reviewed repository head. No blank-origin reachability or BB(6) halting decision. Programme: [R-20261103T013400Z-agent8-623-inverse](../../research/issues/R-20261103T013400Z-agent8-623-inverse.md). Earlier [pilot](TernaryInverse.lean) established the exact ninefold drain pumping. Its source-anchored counterpart [TernaryInverseSource.lean](TernaryInverseSource.lean) imports unchanged [Google DeepMind Cryptids at c86f15861709b76042998c5211c7b2f83991621b](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean).

## Exact theorem statements

Write `D(a,d)` for the two-counter Poincaré section and `T` for the accelerated high-level map. For each natural `q`, define four **distinct** configurations:

```text
A(q) = D(486q+42, 486q+45)
B(q) = D(486q+42, 486q+46)
C(q) = D(486q+44, 486q+40)
E(q) = D(486q+44, 486q+44)
```

The structural formulas hold **for all q >= 0**, including every failing transition:

```text
T(A(q)) = drainB(2, 2q, 1452q+138)
T(B(q)) = drainB(0, 2q, 1452q+143)
T(C(q)) = drainB(0, 6q, 1440q+140)
T(E(q)) = drainB(0, 6q, 1440q+140)
```

Thus `T(C(q)) = T(E(q))` unconditionally, whether that common successor is `none` or a surviving `D` state. The companion program [TernaryCollision.lean](TernaryCollision.lean) gives exact source-matched Lean proofs `a_step`, `b_step`, `c_step`, `d_step`, and `pair_CD`. The proof directly expands all seven high-level branches and the relevant intermediate `evalA` calls. There is no finite-horizon assumption.

### Universal 9-adic transport, including halting

For a `D(a,d)` output, let `shift_z(D(a,d)) = D(a,d+z)`, and extend it to `Option` by `Option.map`. The source-matched Lean lemmas `evalA_shift`, `drainB_shift`, and `drainB_scale_nine` imply that **for all positive q** and each of the four families `F in {A,B,C,E}`:

```text
T(F(9q)) = Option.map (shift_(11664q+2)) (T(F(q))).
```

This is an exact conjugacy-like renormalization along multiples of 9. Both `some` outputs and `none` propagate, with the same shift across all four inputs. In particular, once two or four outputs coincide at positive `q`, their descendants at `9q,81q,...` coincide. The identity does **not** extend to `q=0`; the positivity condition is mathematically essential.

### Infinite four-way successful collision

For every natural `n`, putting `q = 9^n` yields:

```text
T(A(9^n)) = T(B(9^n)) = T(C(9^n)) = T(E(9^n))
          = some (D(0,1458*9^n+2*n+144)).
```

This is theorem `four_pulses`, combining the unconditional reductions, two exact drain identities at base block counts 2 and 6, and closed pumping gains. At `n=0`, four different inputs `D(528,531)`, `D(528,532)`, `D(530,526)`, `D(530,530)` all return `D(0,1602)`. This replaces the earlier finite experimental conjecture by an all-depth proof.

### Infinite four-way synthetic halting collision

At `q=16`, all four inputs map to `none`, certified by finite kernel decision. `allNone16_pulse` applies the same unconditional ninefold transfer to prove:

```text
For every n >= 0:
T(A(16*9^n)) = T(B(16*9^n)) =
T(C(16*9^n)) = T(E(16*9^n)) = none.
```

These are synthetic section states. The theorem does not say that the blank-origin orbit reaches any of them.

## Stronger: positive-density halting cylinder

The sparse four-way halting family above belongs to a **full arithmetic progression**. The local kernel theorem `four_halt_residue` proves, for every natural `r`:

```text
T(A(27r+16)) = T(B(27r+16)) = T(C(27r+16)) = T(E(27r+16)) = none.
```

More generally, `b_halt_residue` and `c_halt_residue` prove `T(B(9r+7)) = T(C(9r+7)) = none` for all `r`; `pair_CD` extends the same statement to `E`. The strict `A` failure is forced at `q=27r+16` by its direct `evalA 2 (54r+31)` term, which reads the ternary digit pattern `31 mod 27 = 4`. The `B,C,E` branches fail after one or two further `drainB` evaluations, with `evalA 0 (6r+3) = none`. All proofs are symbolic reductions using explicit residue equalities and quantified natural parameters, **without finite sampling**. The `#print axioms` audit for `four_halt_residue` is `[propext, Quot.sound]`.

The progression covers one of every 27 natural parameter values in the synthetic four-state family, a positive natural density, and therefore strengthens the preceding ninefold halting pulse result. No claim is made that this proportion describes the blank-origin orbit. The source-imported copy passed full unchanged-source Lean CI 41676854489.

## Verification and reproducibility

- [TernaryCollision.lean](TernaryCollision.lean): fully self-contained Lean 4.36.0-rc2 definitions faithfully copied from the pinned original source, plus the complete collision and transport proofs. Tested by local Lean kernel with **no `sorry`, custom axioms, `native_decide`, or fuel cutoffs**. The `#print axioms` audit for `four_pulses`, `pair_CD`, `scale_A`, `scale_C`, `pair_preserved_A_B`, and `allNone16_pulse`, plus `four_halt_residue`, lists only `[propext, Quot.sound]`.
- [TernaryInverseSource.lean](TernaryInverseSource.lean): same new theorems restated directly on original Cryptids `evalA`, `drainB`, `highLevelNext`, and `HighLevelState`, alongside the source-anchored original pumping theorem. This file is compiled by the [existing manual source-pinned verifier](../../.github/workflows/agent49-623-parity-source.yml), which clones the exact SHA and builds its raw Turing-machine acceleration. Previous run [41562329111](https://github.com/FlareZ123/bb6/actions/runs/41562329111) passed **before the collision theorems were added**. The attempted new run [41592311563](https://github.com/FlareZ123/bb6/actions/runs/41592311563) failed in approximately two seconds before any visible job step or available logs; the second attempt failed similarly, concurrently with failures across unrelated workflows. **Resolved 2026-11-03:** The later complete [manual run 41676854489](https://github.com/FlareZ123/bb6/actions/runs/41676854489) succeeded. Its `source-parity` job compiled the unmodified upstream #623 module, then ran `lake env lean Agent8TernarySource.lean` successfully. All original-source collision, transport and residue-halt theorems in this dossier are consequently source-authenticated. The full Lean axiom-audit directives are retained in the compiled file. This verification changes provenance and confidence, not the unresolved blank-root outcome. See [CI warning](../../communications/broadcast/2026-11-03T065600Z_agent8-ci-runner-failures.md).
- The distinct families and constants were independently checked by an exact integer evaluator during discovery, then superseded by the universal Lean proofs. All claims above are about the accelerated arithmetic map; the original source contains the established raw-machine-to-`D(0,7)` halting equivalence.

## Significance, limitations, next research obligation

The high-level transition is demonstrably noninjective on arbitrarily large surviving and halting inputs. The translation identity gives a uniform method to lift arbitrary inverse collisions and halting examples to infinitely many different input states. Consequently, reverse searches relying on uniqueness, one-to-one predecessor classes, or a finite cutoff without congruence controls are unsound.

**BB(6) remains unsolved.** Neither collision family has been proved reachable from the genuine blank-origin start `D(0,7)`. In fact, source-checked Agent49 parity and mass-growth results confine any blank-origin halting event to a strict diagonal corridor without deciding whether that orbit ever enters the fatal gate. To approach an actual halting decision, the inverse grammar needs an invariant tied to *genuine blank-reachable* histories or a source-checked complementary upper-bound argument. Academic novelty and independent reviewer assessment are pending; retain this material in `im-results/` unless a mathematical advance is independently established.


## Source-level first-coordinate translations and sharp ternary drain budget (2026-11-03, Agent 8)

Both new modules refer directly to the original DeepMind [#623 source at commit c86f1586](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean). Their statements concern arbitrary accelerated configurations. They do **not** decide blank-root halting.

### Affine translation identities

[TernaryFirstSource.lean](TernaryFirstSource.lean) proves that for b<a, adding a natural t to the initial first counter of the B-drain adds exactly t to the terminal first counter, leaving the terminal third counter unchanged. The proof transports the first counter through every evaluator call and applies strong induction on the decreasing B-index.

This yields two exact far-left rays of the complete transition T: for any t≥0 and odd d with a>2d+8, T(D(a+t,d)) equals the first-coordinate translation by t of T(D(a,d)); for even d, the same holds when a>2d+4. There is no first-counter parity assumption in these two statements.

The module also contains two far-right rays, locally Lean 4.36.0-rc2 checked: if a is positive and even, then for odd d≥2a+1 or even d≥2a+2, changing the input from D(a,d) to D(a,d+2t) translates the output first counter by 2t and preserves its second counter. These last two theorems await the next successful source-pinned CI run.

**Source certification:** [CI run 41716622142](https://github.com/FlareZ123/bb6/actions/runs/41716622142), job 126198203096, compiled the unchanged Cryptids accelerator and the first-source module with both far-left identities. The subsequent far-right additions were committed after the certified head.

### Universal sharp B-drain growth

[TernaryBudgetSource.lean](TernaryBudgetSource.lean) contains exact Lean proofs for the original source; a separately implemented source-matched Lean 4.36.0-rc2 file has compiled all statements with standard foundational axioms and no sorry.

* Every successful evaluator E(a,k,m)=(a′,b′,d′) satisfies m+k≤d′+3b′+2.
* Every successful drain B(a,b,d)=D(a′,d′) satisfies d′≥d+3b, without an input first-counter or parity assumption.
* The third-coordinate bound has a **complete equality classification**. Define b₀=0 and bₙ₊₁=3bₙ+3; equivalently 2bₙ+3=3ⁿ⁺¹. For every a,d,n, the exact formula B(a,bₙ,d)=D(a+n,d+3bₙ) holds, including a=0. Conversely, if any successful drain attains d′=d+3b, its block index b necessarily equals bₙ for some n. The theorem drainB_d3_exact_iff states this equivalence without a finite cutoff.

The equality indices are 0,3,12,39,120,363,1092,3279,...; in ternary they are 0,10,110,1110,... . A strict evaluator potential inequality for every non-2 final ternary digit proves that these are the only equality cases. Independent exact integer testing of the first 200,000 canonical safe drains was consistent with the full theorem, while the Lean proof itself is universal.

The budget implies d′≥3d+14 on the odd far-left branch of T and d′≥3d+8 on the even far-left branch whenever these branches complete successfully. Along the far-left affine rays the output second counter depends only on the input d, reducing large-family inverse searches to a one-variable equation. These results do not exclude any blank-reachable terminal window by themselves.

The equality indices are repeated ternary 1s followed by a zero, complementing the repeated-1-and-final-2 first-failure threshold in [Agent49's work](../agent49-parity623/README.md). Comparing these two exact languages may support a stronger rooted predecessor exclusion theorem. Keep both modules in intermediate results until relevance to the BB(6) frontier is established.


## 2026-11-06: gate-parent envelope and ray-residue reductions

The new `GatePredecessorSource.lean` imports the original #623 parity
transition and the affine predecessor bounds. It proves
`blank_run_gate_parent_finite_envelope`: apart from the two small states
(D(4,5)) and (D(4,7)), any state in the logarithmic gate that halts must
have its immediate predecessor in one of four explicit old-cone affine
sectors. The source-level theorem passes the pinned
`agent49-623-ternary-shift.yml` CI (run 17).

The same Lean file contains
`positive_gap_residue_exponent_unique`. For a fixed odd base constant (N),
there cannot be two exponents (A<B) with
(N\bmod3^{A+1}=3^A) and (N\bmod3^{B+1}=3^B). This formalizes the
positive-gap uniqueness reduction.

`NegativeGapResidue.lean` formalizes the complementary negative-gap
separation lemma: if
[
(C-2A)\bmod3^{A+1}=3^A,\qquad
(C-2B)\bmod3^{B+1}=3^B,
\]
with (A<B) and (2B\le C), then (B-A\ge2\cdot3^A). The proof was
checked locally with Lean 4.36.0-rc2; repository CI verification was added
in run 18 and is pending at the time of this note.

`FirstEvalRayResidues.md` gives the exact five first-evaluator cases for
even first coordinate (b), including the positive-gap 3-adic valuation
criterion and the negative-gap exponent-spacing argument. These are
**first-call** conditions only. A successful first evaluator does not imply
that the remaining `drainB` recursion succeeds; for example, (D(12,12))
passes `evalA 1 12 29) and then fails at `evalA 0 3 42).

A separate BigInt translation of the source transition audited the first
1,000 blank-root states. It found 419 right-ray and 259 left-ray old-cone
states, with 222 candidate first-call failure shifts and no equality between
an actual root parameter and a candidate. The closest candidate distances
were 38 on a right ray at index 13 and 126 on a left ray at index 11. This
is computational evidence from an independent translation, not a
kernel-checked 1,000-state proof.

The next root-specific proof target is to derive a separation invariant
between the actual ray parameter and every first-call failure candidate
directly from the preceding `drainB` digit updates. A complete proof must
also control later drain iterations after a successful first call. These
reductions do not determine BB(6).

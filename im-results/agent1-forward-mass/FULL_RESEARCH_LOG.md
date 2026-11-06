# Historical full research log

**Unabridged snapshot of the former research README, 6 November 2026.** Mathematical derivations, failed approaches, source references, finite data and chronology are preserved. Dated “pending”, “current” and “next” statements below refer to their original time and may be superseded. Use the maintained [summary](README.md) for current synthesis.

---

# Machine C: a kernel-checkable forward mass-cutoff certificate

**Status 2026-11-03:** An alternative reproduction of an earlier Agent1 m8 result plus a sharper positive-right mass-growth classification. Lean 4.36.0-rc2 source-original verification of the sharp mass, blank-orbit growth and fixed-target decider **succeeded** in [manual CI 41670293123](https://github.com/FlareZ123/bb6/actions/runs/41670293123). The alternative 147-chunk forward trace has a local source-shape proof, while the prior 16-segment m8 trace is now independently **original-source CI-certified** in [run 41670233031](https://github.com/FlareZ123/bb6/actions/runs/41670233031). This is a bounded-method/one-gate research pilot, not a complete Machine C nonhalting result or a BB(6) bound. The code and generator are reproducible. Keep this in `im-results/` pending original-source compilation and independent assessment.

## Prior-art correction identified 2026-11-03 10:02 UTC

**Important duplication:** Before this invocation, an earlier Agent 1 incarnation had already completed a *different*, locally kernel-checked forward certificate of the **same** Machine C m=8 terminal gate, with the **same** 150052-return endpoint and all lower-mass terminal exclusion. Read [Agent1's earlier m8 trace dossier](../agent1-c-m8-trace/README.md), [M8TraceBridge.lean](../agent1-c-m8-trace/M8TraceBridge.lean), and [M8TraceCert.lean](../agent1-c-m8-trace/M8TraceCert.lean). Those files are also awaiting a successful unchanged-original-source CI run and were already integrated into the existing [Agent3 manual workflow](../../.github/workflows/agent3-c-bounce-inverse.yml). The present 147-chunk proof is an **alternative independent checker/reproduction of that earlier local result**, and must not be counted or advertised as a newly decided m8 gate. Its additional self-contained mass proof is useful validation infrastructure, but the m8 result was **known internally before this pilot**. The new programme admission originally overlooked this prior artifact, now corrected without erasing the consumed slot or evidence.

**Other overlap:** Agent3 had already source-formalized the **existence of a fixed-target finite reachability decider** using the weaker growth bound `a+2k≥7+2n` in [SectionMassOrbit.lean](../agent3-c-bounce-inverse/SectionMassOrbit.lean). Our `CFiniteReach.lean` and `OriginalFiniteReach.lean` specialize the same concept with a **halved search horizon** from `(a+2k-7)/2` to `(a+2k-7)/4`; the decidability claim is prior work. The potentially separate new mathematical content is the **all-input exact increment classification** `+2 ↔ k=0,a≥2`, `+4 ↔ k>0, a≥2k` and sharpened **true blank-orbit +4 index bound**. Their correctness has been checked against copied complete source definitions; **original unchanged-source import compilation and independent novelty checking are still outstanding.** These strengthened inequalities do not decide a Machine C holdout or BB(6).

## Exact question and previous baseline

For the original Agent46 Machine C first-return map `BB6.Agent46.secNext`, started at authentic blank section `(5,1)`, can we prove **no section ever equals `(1,524260)`**? In addition to Agent1's earlier forward m8 certificate linked above, Agent34's [separate backwards certificate](../agent34-c-low-mod32/README.md) computed a 41-state inverse cone but did not kernel-certify that graph. Agent34 also independently reported a forward mass crossover at return 150052. The current forward certificate uses a different proof mechanism: an exact finite initial trajectory and globally proven monotonicity.

The target is one of Agent46's low halting-section inputs indexed by m=8:
`K_8+3*8+4=2^(2*8+3)`, hence `K_8=524260`.
It has weighted mass `a+2*k=1048521`. It is a **terminal input** for the original section map. Neither an arbitrary halting input nor a halting machine runtime is established by this target alone.

## Main conditional theorem and proof architecture

`ForwardMass.lean` gives a generic theorem `terminal_overshoot`, locally kernel-checked, standard axioms `[propext, Quot.sound]`:

For any deterministic Option-valued step function with weakly nondecreasing natural mass along successful steps, if (i) the orbit from start is still alive at time N with mass M, and (ii) a terminal target has strictly smaller mass than M, then **the orbit never reaches the target at any time**. If it hit earlier, it could not continue to N; if it hit later, monotonicity forbids mass loss.

`FastC.lean` implements a structurally fuel-recursive projected bounce, avoiding slow reductions of the original elapsed-time-carrying well-founded bounce. `ForwardOriginal.lean` proves the **uniform all-input equivalence** of FastC bounce/step with the *imported* original `FastSectionDef.lean`; imports `SectionMassStrict.lean` for the original source theorem `section_mass_strict`; then derives `all_terminal_lower_mass_unreachable` and `m8_low_gate_unreachable`. The latter two are currently **source-integration claims awaiting original import compilation**. The same bridge proof compiled against a locally reconstructed definition whose complete body was independently transcribed from the original `BounceCalc` and `FastSectionDef` sources, producing standard axioms only, but a copied source is not proof of the original dependency chain.

The original-source theorem intended for CI has precise statement:

```lean
theorem m8_low_gate_unreachable :
    ∀ n, ForwardMass.run BB6.Agent46.secNext (5,1) n ≠ some (1,524260)
```

The more general theorem would exclude **every terminal section input** `(a,k)` with `a+2*k < 1048525` from the genuine `(5,1)` orbit. It does **not** prove that every such input is terminal.

## Deterministic finite computation

The exact independently transcribed Python `generate_fast_certificate.py` computes 150052 original-equation section returns and generates 147 kernel-proved chunks with at most 1024 returns per chunk. The final state is `(621619,213453)`, weighted mass **1048525**, the first mass exceeding the target mass **1048521**. Its weighted growth is at least 2 on all simulated transitions. No earlier section equals the target, but the final *proof* does not rely on trusting this Python observation: each chunk uses Lean `by decide`, and 147 chain lemmas use the generic composition theorem.

Canonical SHA256 of the newline-delimited complete state trace `n,a,k\n` for n=0..150052 inclusive:

```text
d82b4a6b23f9f769c144400bebd51428050778bdc437bf17e6bb61561585e14a
```

`generate_fast_certificate.py` requires Python 3.10+ and the `filelock` library. It emits `manifest.json`, `FastChunks00.lean` through `FastChunks14.lean`, and `FastPrefix00.lean` through `FastPrefix14.lean`. Generated files are deterministic and use advisory locking and atomic replacement. The 30 generated Lean files are reproducible outputs and therefore intentionally omitted from version control in favor of the generator. `FastCChunks.prefix_147` concludes the exact full-trace equality, with `#print axioms` reporting only `[propext, Quot.sound]`.

Local Lean 4.36.0-rc2 compiled all 15 fast chunk groups and all 15 prefix modules in the original proof run. The generic cutoff theorem, all-input fuel/section bridge against a full source-equation reconstruction, and exact terminal test likewise compiled with standard axioms only. This is **local verification**, not a successful full-repository source CI run.


## Stronger self-contained local certification

The compressed ASCII artifact [StandaloneLean.tar.gz.b64](./StandaloneLean.tar.gz.b64) contains five complete local Lean sources: `ForwardC.lean` (literal source-equation well-founded bounce/section), `FuelBridge.lean` (total proof of equivalence with the fuel evaluator), `ForwardTransfer.lean` (complete return-trace transfer and terminal test), `ForwardCSectionMass.lean` (direct structural proof that all successful source-equation sections increase weighted mass by at least 2), and `ForwardStandalone.lean` (all-time reachability exclusion). Decode base64, decompress gzip, and extract the tar members into the same working directory as the generated chunk modules. The compressed tar's SHA256 is `61e16189c7480447ee58d397b6c36e78da44d04f6db35e068296d2f0e5073392`.

Under Lean 4.36.0-rc2, the following **self-contained mathematical model** theorems compile with the exact axiom audit `[propext, Quot.sound]`, with no `sorry`:

- `ForwardC.section_mass_strict`: for all successful transcribed sections, `a+2*k+2≤x+2*y`.
- `FuelBridge.next_correct`: the complete fuel-driven `FastC.next` equals the transcribed source-equation `ForwardC.secNext` **for all natural inputs**, with no finite domain restriction.
- `ForwardTransfer.source_trace`: the full certified 150052-return trajectory under those transcribed equations.
- `ForwardStandalone.model_m8_gate_unreachable`: all-time exclusion of the m=8 terminal input from the **transcribed** blank-start section orbit.
- `ForwardStandalone.model_all_small_terminal_unreachable`: the corresponding exclusion for every terminal state of transcribed mass strictly below 1048525.

The transcribed `ForwardC.bounce` and `secNext` equation bodies are identical to the observed published `BounceCalc.lean` and `FastSectionDef.lean` definitions at the time of this investigation. Establishing that connection via an imported-source Lean compilation remains a separate obligation; copied definitions alone must never be cited as an original-source kernel certificate. The standalone theorem greatly narrows that final obligation to a short semantic-identification bridge.

## Verification workflow and remaining obligations

1. Reconstruct the generated proofs with `generate_fast_certificate.py`, compile `ForwardMass.lean`, `FastC.lean`, then each pair `FastChunksNN.lean`, `FastPrefixNN.lean` in increasing NN order using Lean 4.36.0-rc2. Set Lean's module search path to include the artifact directory.
2. Add unchanged repository dependencies `BounceCalc`, `FastSectionDef`, `SectionMassStrict` and the original module dependency chain, and compile `ForwardOriginal.lean` against **the actual originals**, without rewriting names, stubbing the source, or adding axioms. Record the complete successful build revision and `#print axioms` for `m8_low_gate_unreachable`. The GitHub Actions service was returning before-step failures in the Critic's [08:04 UTC incident](../../communications/broadcast/2026-11-03T0804Z_critic-source-grade-ci-gate.md); no success claim is made for this final check.
3. Independently review semantic linkage of the authentic blank machine to its first section `(5,1)`, and reconcile whether this fixed-gate exclusion is already entailed by prior original source theorems. Exact upstream inputs are [Agent46's map](../agent46-c-jump/FastSectionDef.lean), [source mass theorem](../agent3-c-bounce-inverse/SectionMassStrict.lean), and [Agent34's prior pilot](../agent34-c-low-mod32/README.md).
4. A future second-root transfer must choose a genuinely distinct section map and demonstrate the source/mass bridge, rather than merely append a longer finite trace.

**Limits:** No full Machine C nonhalting classification, no new exact BB(6) value, no global six-state upper bound and no primitive-step halting witness follow. The current published research objective remains open.


## Additional structural bound: sharp minimum mass increment on the blank orbit

A second independent derivation found that the weak `+2` global source bound can be sharpened to **`+4` on every successful section with a positive right counter**, and the exact equality case for `+2` is only `a≥2, k=0`:

```lean
theorem section_mass_four_if_right_positive (a k x y : Nat)
  (hk : 0<k) (h : secNext (a,k)=some (x,y)) :
  a+2*k+4 ≤ x+2*y

theorem section_delta_two_iff_right_zero (a k x y : Nat)
  (h : secNext (a,k)=some (x,y)) :
  x+2*y = a+2*k+2 ↔ 2≤a ∧ k=0
```

Both source-body proofs are in [PositiveMassOriginal.lean](./PositiveMassOriginal.lean), tested locally with an independently recreated **exact full source-map and original mass theorem** and reporting standard axioms only. They use `bounce_even_mass_lower` and `bounce_odd_mass_lower` to retain the quantified recursive branch coverage.

Agent38's already source-CI-certified [blank_section_positive](../agent38-c-section-mod4/Agent38SectionParity.lean) proves every genuine blank-reachable section has positive right counter. Therefore the two results compose to a proposed **all-time original-source theorem**:

```lean
BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) = some (a,k)
  → 7 + 4*n ≤ a + 2*k
  → n ≤ (a+2*k-7)/4
```

The formal induction is provided in [BlankMassFour.lean](./BlankMassFour.lean). **Original-source imported build is pending.** Its local syntax test used an axiom placeholder solely for Agent38's previously CI-certified theorem, so the test must not be described as an authenticated no-new-axioms source result. In contrast, [BlankMassStandalone.tar.gz.b64](./BlankMassStandalone.tar.gz.b64) contains a **fully kernel-checked, axiom-audited standalone source-equation model proof** of the strengthened bound with original bounce-output positivity established directly. That compressed tar contains `PositiveMass.lean`, `RightPositive.lean`, and `BlankMassStandalone.lean`, with gzip SHA256 `880ab5f894ce318748c196fda0ac38914e8181023e012ef3b6f1720ce71c0214`. Its `blank_mass_four` and `blank_index_bound` use only `[propext, Quot.sound]`, no sorry.

This gives an exact necessary time-index bound for arbitrary reachable section states and improves the primitive monotonicity inequality without lengthening any finite trace. It does not decide any infinite halting family. Agent38 was asked for source verification and independent novelty review in [the direct mailbox](../../communications/agent38/2026-11-03T0951Z_agent1-sharp-blank-mass-four.md).


A further exact branch classification is proved in [ExactDeltaFour.lean](./ExactDeltaFour.lean):

```lean
theorem section_delta_four_iff_direct (a k x y : Nat)
  (h : secNext (a,k)=some (x,y)) :
  x+2*y=a+2*k+4 ↔ 2≤a ∧ 0<k ∧ 2*k≤a
```

Thus, across all successful Machine C section returns, mass increase **exactly 2** occurs only at `a≥2,k=0`, while increase **exactly 4** occurs only on the positive-right nonbounce branch. Every other successful return increases the mass by at least 5. Both exceptional-branch equivalences were checked locally under the exact original-source map shape with ordinary foundational axioms `[propext, Classical.choice, Quot.sound]`. These are **source-body verified locally, authentic original import CI pending**.


## Exact finite decider for any individually specified section target

The strengthened blank-origin bound also gives a **complete decision procedure for each fixed target** `(a,k)`. Any occurrence must be at a section index `n ≤ (a+2*k-7)/4`. Consequently, consider the computable Boolean

```lean
def reachableBool (a k : Nat) : Bool := decide
  (∃ i : Fin ((a+2*k-7)/4+1),
    ForwardMass.run ForwardC.secNext (5,1) i.val = some (a,k))
```

The complete correctness equivalence with *unbounded* existence is kernel-checked in [CFiniteReach.lean](./CFiniteReach.lean), with `[propext, Quot.sound]` and no `sorry`. Smoke calculations for targets `(5,1)`, `(3,4)`, `(1,4)`, `(4,7)`, `(5,2)` give `true,true,false,true,false` respectively. [OriginalFiniteReach.lean](./OriginalFiniteReach.lean) is its true-original-import form, locally syntax-checked against exact source-shaped substitutes and pending authentic repository compilation. The decider is **not uniformly efficient** as target mass grows, and establishing that *every member of an infinite dyadic target family* is unreachable remains the open Machine C problem. This finitary target decidability does not imply a global BB(6) result.


**Independent cross-certificate agreement:** the present 147-chunk trace was also replayed numerically at all **16 original 10,000-return milestones** (including the final 52-return segment), using the endpoint list from [the earlier Agent1 M8TraceCert.lean](../agent1-c-m8-trace/M8TraceCert.lean). All 16 independently regenerated states matched exactly. This is a reproducibility cross-check and strengthens confidence in the trace input data; it does not substitute for a source-authenticated theorem or make the repeated m8 decision novel.

## 2026-11-03 16:04 UTC: authentic-original-source certification completed

The previous caveats about **pending source verification of the sharp mass and fixed-target theorems** are superseded by successful [manual GitHub Actions 41670293123](https://github.com/FlareZ123/bb6/actions/runs/41670293123) (job 126036551654, source commit `a9f694f99b3b952792bc58338e162b53961da5a3`). The unchanged actual Lean source modules `BounceCalc`, `FastSectionDef`, `SectionMassStrict`, `Agent38SectionParity`, `GenericSection` and their original dependencies were compiled first under pinned Lean 4.36.0-rc2. The checked modules were:

- [PositiveMassOriginal.lean](PositiveMassOriginal.lean): every defined positive-right edge increases weighted mass by at least 4; exact delta 2 iff `a≥2,k=0`.
- [ExactDeltaFour.lean](ExactDeltaFour.lean): exact delta 4 iff `a≥2,k>0,2k≤a`.
- [BlankMassFour.lean](BlankMassFour.lean): every genuine blank-origin section return at index n satisfies `7+4*n ≤ a+2*k`, hence `n≤(a+2*k-7)/4`.
- [OriginalFiniteReach.lean](OriginalFiniteReach.lean): `reachableBool_correct`, an exact finite decider for **any fixed section target** with that improved cutoff.

All printed final axiom audits are `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. This certifies the **original-source integration** of the structural theorems previously checked only against copied definitions. It does not certify any global machine halting or nonhalting claim, nor establish novelty over the full literature.

The *older* [M8TraceBridge/M8TraceCert](../agent1-c-m8-trace/README.md) were independently compiled **against unchanged authentic imports** in successful [manual CI 41670233031](https://github.com/FlareZ123/bb6/actions/runs/41670233031), job 126036343299. This proves the all-time m8 blank-section exclusion and terminal rank cutoff. This is source verification of a previously locally kernel-checked mathematical result, not a new gate found by extending the 147-chunk duplicate. The alternative 147-chunk `ForwardOriginal.lean` remains a separate, optional source-bridge candidate; it is unnecessary for the now-proved m8 result.

**Scientific next step:** derive a parameter-uniform restriction on the two infinite authentic halting families, particularly the unbounded dyadic gates where the fixed-target bound only furnishes a finite search for each individual target. Do not multiply isolated m8-style finite certificates without a genuine method for the full infinite locus.

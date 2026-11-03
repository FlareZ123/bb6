# Machine C: a kernel-checkable forward mass-cutoff certificate

**Status 2026-11-03:** Lean 4.36.0-rc2 local source-shaped proof and complete 147-chunk calculation succeeded, with original **unchanged-source integration pending**. This is a bounded-method/one-gate research pilot, not a complete Machine C nonhalting result or a BB(6) bound. The code and generator are reproducible. Keep this in `im-results/` pending original-source compilation and independent assessment.

## Exact question and previous baseline

For the original Agent46 Machine C first-return map `BB6.Agent46.secNext`, started at authentic blank section `(5,1)`, can we prove **no section ever equals `(1,524260)`**? Agent34's [separate backwards certificate](../agent34-c-low-mod32/README.md) computed a 41-state inverse cone but did not kernel-certify that graph. Agent34 also independently reported a forward mass crossover at return 150052. The current forward certificate uses a different proof mechanism: an exact finite initial trajectory and globally proven monotonicity.

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

## Verification workflow and remaining obligations

1. Reconstruct the generated proofs with `generate_fast_certificate.py`, compile `ForwardMass.lean`, `FastC.lean`, then each pair `FastChunksNN.lean`, `FastPrefixNN.lean` in increasing NN order using Lean 4.36.0-rc2. Set Lean's module search path to include the artifact directory.
2. Add unchanged repository dependencies `BounceCalc`, `FastSectionDef`, `SectionMassStrict` and the original module dependency chain, and compile `ForwardOriginal.lean` against **the actual originals**, without rewriting names, stubbing the source, or adding axioms. Record the complete successful build revision and `#print axioms` for `m8_low_gate_unreachable`. The GitHub Actions service was returning before-step failures in the Critic's [08:04 UTC incident](../../communications/broadcast/2026-11-03T0804Z_critic-source-grade-ci-gate.md); no success claim is made for this final check.
3. Independently review semantic linkage of the authentic blank machine to its first section `(5,1)`, and reconcile whether this fixed-gate exclusion is already entailed by prior original source theorems. Exact upstream inputs are [Agent46's map](../agent46-c-jump/FastSectionDef.lean), [source mass theorem](../agent3-c-bounce-inverse/SectionMassStrict.lean), and [Agent34's prior pilot](../agent34-c-low-mod32/README.md).
4. A future second-root transfer must choose a genuinely distinct section map and demonstrate the source/mass bridge, rather than merely append a longer finite trace.

**Limits:** No full Machine C nonhalting classification, no new exact BB(6) value, no global six-state upper bound and no primitive-step halting witness follow. The current published research objective remains open.

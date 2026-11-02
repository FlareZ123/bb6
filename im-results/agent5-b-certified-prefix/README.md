# Agent 5: finite kernel-certified third sampled parity for Machine B

**Classification:** intermediate finite computation. This does not decide the Machine B holdout, prove infinite nonhalting, or improve a global BB(6) bound. The first three sampled cycles were already reported computationally by Agent 5. The contribution here is a reproducible, proof-kernel-checkable certificate for the otherwise enormous third sample.

Machine B: `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`.

The original-source Lean semantics and whole-machine iff criterion were established independently by Agent 18 and collaborators: [the scalar reduction](../agent18-b-cycle/ONE-DIMENSIONAL.md) and [CI 41393439663](https://github.com/FlareZ123/bb6/actions/runs/41393439663). The recursively sampled map is

```text
G(z) = 3*(z/2) + 4 + 5*(z%2)
A(0) = 3
Z(n) = G^[A(n)](0)
A(n+1) = Z(n) + 9 - 3*(Z(n)%2)
raw machine halts iff exists n with Z(n)%2 = 0.
```

The exact finite statement here is `forall n<3, Z(n)%2=1`. In particular, `A(1)=25`, `A(2)=227097`, and `G^[227097](0)%2=1`. The last integer has **132847 bits**, with SHA256 of its unsigned big-endian byte representation `15d1bf0d327f41d76b4a47e6d5293cab98143a69ae12c70487be42a23f3593cc`. Its value is never trusted as an axiom: each chunk is checked by Lean's ordinary kernel via `by decide`.

## Reproduction and proof structure

- `BTraceCore.lean` defines the exact scalar map and proves `iterG_add`.
- `make_certificate.py` generates 28 modules, each with a concrete large natural value, a kernel-checked block of at most 8192 scalar iterations, and an exact cumulative-prefix theorem. Generated source files are disposable and deliberately excluded from Git: they are deterministic outputs of the committed generator.
- `BTraceFinal.lean` (generated) proves the third sampled parity using the 28 prefix certificates and establishes the first two samples.
- `BTraceSource.lean` proves definitional equality to Agent 18's original unmodified `OneDim.G` and `iterG`, verifies `scalarA 1=25` and `scalarA 2=227097`, and states `first_three_samples_odd` for every `n<3`.
- The **manual-only** workflow `.github/workflows/agent5-b-certified-prefix.yml` imports the unmodified `BReduction.lean` and `BOneDim.lean` under pinned Lean 4.36.0-rc2, regenerates and compiles all 28 proof chunks, and checks `BTraceSource.lean`. It does not run on commits and preserves the CI policy.

Local verification on 2026-11-02: all 28 generated modules, final parity theorem, and the source-bound theorem against an exact signature-matching mock compiled with Lean 4.36.0-rc2. The terminal proof had axiom set `[propext]`; the mock-composed all-first-three theorem had `[propext, Quot.sound]`, with no `sorryAx`. This is not a claim of independent full-source verification until the manual workflow succeeds.

The basic arithmetic facts about this sample are substantial finite evidence only. The unresolved statement remains deciding whether **any** future recursively sampled parity is zero, an infinite quantified question unaffected by three verified examples. Further research should prioritize a special-orbit invariant or uniform sampled recurrence and avoid merely extending the computational horizon.

## Fully certified original-machine finite-time lower bound (2026-11-02)

The manual [original-source CI run 41463626001](https://github.com/FlareZ123/bb6/actions/runs/41463626001) **passed**. It pins Google DeepMind Cryptids revision `ced8f9f44f67a167d5ecc03e687b048c67926371`, installs the upstream Lean 4.35.0-rc4 and Mathlib cache, builds the **unmodified** published six-state Turing machine certification, imports the unmodified Agent18 reduction and semantic bridge, then checks every one of our 28 generated chunks and all of `BTraceSource.lean`, `BTraceReach.lean`, `BTraceMagnitude.lean`, `BTraceRuntime.lean`, `BTraceRaw.lean`.

The actual Lean theorems establish:

1. `first_three_samples_odd`: each of the first three dynamically sampled scalar parities is 1, with `scalarA 2=227097`. Each preceding cycle therefore survives. `original_three_cycles_survive` proves genuine accelerated reachability `Star (3,0,0) (resetA 3,0,0)`.
2. `third_sample_bits`: the enormous third sample is in the exact interval `2^132846 ≤ iterG 227097 0 < 2^132847`, and `fourth_reset_lower` gives `2^132846 ≤ scalarA 3`.
3. `giant_postreset_prefix`: every `n<2^132846` admits `n` defined accelerated steps from fourth reset. The first counter cannot decrease by more than one on a defined accelerated action.
4. Most significantly, `raw_blank_below_fourth_reset` proves in the **original upstream raw six-state machine semantics** that for every natural `n < scalarA 3`, there exist a natural `m≥n` and raw configuration `c` with `ReachesIn Source.target m (init []) c`. This transports the giant finite lower bound to literal primitive TM transitions starting from the blank tape, because each accelerated step is an upstream-certified `ReachesPlus` of at least one raw transition.

The final original-raw theorem's `#print axioms` is exactly `[propext, Classical.choice, Quot.sound]`. The other generated and source-level theorems use subsets of these standard axioms. No `sorryAx`, untrusted extracted witness, or `native_decide` is present. Generator output is checked in the Lean kernel; its Python arithmetic is not treated as proof.

The result is a large **finite-machine-specific** survival bound, not a Busy Beaver bound improvement: its value is dwarfed by existing six-state record constructions and tells us nothing about the infinite next sampled parity problem. An earlier local-development source mock was used only to catch syntax errors; this successful pinned-upstream CI supersedes that preliminary check.

# Agent 5: finite kernel-certified third sampled parity for Machine B

**Classification:** intermediate finite computation. This does not decide the Machine B holdout, prove nonhalting, or improve a global BB(6) bound. The first three sampled cycles were already reported computationally by Agent 5. The contribution here is a reproducible, proof-kernel-checkable certificate for the otherwise enormous third sample.

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

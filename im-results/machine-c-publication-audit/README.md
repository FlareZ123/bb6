# Machine C publication qualification archive

**Audit by Agent 19, 2026-11-07.** These nine notes were moved from `results/` after comparison with the later repository frontier. Their full contents, proofs, CI references, and provenance are preserved. Their demotion corrects the publication index; it does not invalidate their Lean theorems.

## Why each note is supporting work

| Preserved note | Qualification reason |
| --- | --- |
| [Four mod-1024 reset exclusions](2026-11-02-machine-c-four-new-mod1024-exclusions.md) | All four families are specializations of the earlier source-certified modulus-512 families (38,130,184,271). |
| [Mod-1024 residue 184](2026-11-02-machine-c-mod1024-184-exclusion.md) | A strict subfamily of the source-certified (n\equiv184\pmod{512}) theorem. |
| [Mod-128 residue 6](2026-11-02-machine-c-mod128-six-exclusion.md) | Already covered by Agent 41's modulus-128 quotient exclusions. |
| [Mod-128 residue 18](2026-11-02-machine-c-mod128-eighteen-exclusion.md) | Already covered by Agent 41's modulus-128 quotient exclusions. |
| [Mod-256 residue 31](2026-11-02-machine-c-mod256-thirtyone-exclusion.md) | Already covered by Agent 41's modulus-256 quotient exclusions. |
| [Mod-32 residue 16](2026-11-02-machine-c-mod32-exclusion.md) | Its two modulus-64 lifts, 16 and 48, are in Agent 20's finite reset quotient. |
| [Mod-32 residue 22](2026-11-02-machine-c-mod32-twentytwo-exclusion.md) | Its two modulus-64 lifts, 22 and 54, are in Agent 20's finite reset quotient. |
| [Side mod-16 family](2026-11-02-machine-c-side-mod16-exclusion.md) | The family is included in Agent 20's finite side quotient. |
| [Three symbolic inverse exclusions](2026-11-02-machine-c-symbolic-inverse-exclusions.md) | The families (j\equiv3\pmod{16}), (j\equiv7\pmod{64}), and (j\equiv59\pmod{64}) are all included in Agent 20's finite reset quotient. The reusable inverse lemmas remain useful infrastructure. |

## Retained Machine C result synthesis

The independent residual gateway results are synthesized in [Machine C: source-certified residual gateway exclusions](../../results/2026-11-07-machine-c-gateway-exclusion-synthesis.md). That synthesis retains the 43 reset classes modulo 2048, the five residual reset classes modulo 1024 from the broader four-family source theorem, and the ten residual side classes modulo 512. It distinguishes source-level all-time proofs from the finite quotient's computed cardinalities.

## External prior art

The [Google DeepMind Cryptids Machine C formalization](https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC/) already formalizes the underlying machine acceleration. The inverse exclusions archived here are supporting source-level proofs; no claim is made that the acceleration itself is new or that Machine C has been decided.

# Four source-certified physical B/0 return families for auxiliary #119

**Current status, 9 November 2026.** Four all-parameter primitive-machine return theorems now account for **all 49 previously unclassified B/0 first-return intervals** in the independent ten-million-step physical blank replay of the literal auxiliary six-state machine `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`. All four also carry conditional preservation of the original `NoLeft4 true true false` (left-of-head forbidden `1100`) invariant.

The key result is **mathematical but conditional**. These four return theorems are valid on arbitrary signed tapes for unbounded parameters, provided their explicit input word hypotheses hold. The fact that their hypotheses cover the 49 historical residual intervals is a **finite observation**, not an all-time blank-root reachability theorem. Auxiliary #119 and BB(6) remain open.

## Exact theorem inventory

For `c=(B,h,t)` with `t(h)=0` and natural parameters `n,m`, let `1^k` denote k consecutive tape ones.

| Source theorem | Exact primitive return time | Return head | Conditions and preserved exterior |
| --- | --- | --- | --- |
| `left_gateway_return n` | `14+2n` | `h−8−2n` | Left suffix `t(h−7..h−1)=0100111`, extended alternating word `(10)^n` from `h−8` leftward ending at a zero; all tape at or left of return head unchanged |
| `left_gateway_B_return n` | `14+2n` | `h−8−2n` | Left suffix `0101001`, same alternating extension and zero sentinel; all tape at or left of return head unchanged |
| `right_gateway_return n` | `12+2n` | `h+2n+2` | Left three bits `000`, right `1^(2n)00`; all tape at or right of return head unchanged |
| `double_sweep_return n m` | **`4n+2m+6`** | **`h−2m`** | `t(h−1)=0`, `t(h−2)=1`, right `1^(2n)0`, and a left `m−1`-pair alternating B/1,F/0 retreat ending at zero, `m≥2`; all tape at or left of return head unchanged |

Each endpoint is **B/0** and is produced after exactly the stated number of ordinary Turing machine steps. Exterior tape is universally quantified; no special blank tape outside the listed input corridor is assumed. The double sweep composes a literal 3-step B/0 → F/1 prefix, `n+1` rightward F/1,D/1 pairs, a single F/0 turn to B/1, and `n+m` leftward B/1,F/0 pairs. It is genuinely **two-parameter and unbounded in both directions**. Exact arithmetic is `3 + 2(n+1) + 1 + 2(n+m) = 4n+2m+6`.

The source-certified shield theorems `left_gateway_shield`, `left_gateway_B_shield`, `right_gateway_shield`, and `double_sweep_shield` each conclude existence of that precise physical return with `NoLeft4 true true false` whenever the input has the respective corridor hypotheses and satisfies `NoLeft4 true true false`. Left gateways and the double sweep preserve the entire tape below the returned head. The right gateway shield is proved by an additional induction: each rightward F/D pair writes alternating `01`, and the four-step final tail writes two ones, excluding any newly created left-of-head `1100`.

## Verification against untouched original definitions

The workflow [.github/workflows/agent12-root119-corridor.yml](../../.github/workflows/agent12-root119-corridor.yml) decodes checksum-pinned Lean sources and compiles **unmodified** original `Root119Gate.lean`, `Root119BShift.lean` and `Root119BShield.lean` from [Agent42's dossier](../agent42-root119-guard/README.md). All source declarations are in original `BB6Root119` semantics and use its exact `run`. All theorem axiom reports contain only standard Lean axioms, with no `sorryAx`.

**[Full source-certified Lean 4.36.0-rc2 CI success, run 42588104760](https://github.com/FlareZ123/bb6/actions/runs/42588104760)**

| Decoded source | SHA-256 of original Lean source | Core theorems |
| --- | --- | --- |
| [Root119Corridor.lean.xz.b64](Root119Corridor.lean.xz.b64) | `65efa8844d8836f2579e4d7d5a71f308a2fc2f5343a0c0309f1f0c971ca2ab1d` | Three one-parameter return families, complete tape boundaries |
| [Root119CorridorShield.lean.xz.b64](Root119CorridorShield.lean.xz.b64) | `0888e541438f09ef9da1ea7228d51a2446c488a3b3c42a40a955354acec023ef` | `NoLeft4` transport through all three |
| [Root119Cross.lean.xz.b64](Root119Cross.lean.xz.b64) | `f5dd3f8e6432dec762dbecc1b8c7a791330218bf6c21be4b599fb457606ef99d` | Two-parameter double sweep, exact full tape and `NoLeft4` |

Compressed source is used because the repository already uses source-integrity-pinned Lean B64+XZ artifacts. CI reconstructs ordinary `.lean` files and checks real imports.

## Independent finite trace correspondence

[The standalone Node.js CommonJS 10M test](test-root119-corridors.cjs) simulates all six literal state rows from the blank tape, identifies corridor hypotheses at actual B/0 states, checks that **the next** B/0 arrives at exactly the proved formula's time and position, and audits `NoLeft4 true true false` at inputs and returns.

| Parameterized family | Observed 10M B/0 first returns | Previously unclassified by Agent42 |
| --- | ---: | ---: |
| First left | 21 | 19 |
| Second left | 10 | 10 |
| Right | 18 | 18 |
| Double sweep | 2 | 2 |
| **Total** | **51** | **49** |

The two first-left family starts at raw time 1,275 and 3,638 had already been classified by prior macros; the other 49 are exactly the outstanding `other` set in the existing 10M [Agent42 first-return audit](../agent42-root119-guard/README.md). Every one of 51 observed family inputs and outputs satisfied the shield in the replay.

The two formerly exceptional double-sweep instances instantiate the exact theorem at:

- Start time **4,208**, input B/0 head **−68**, parameters **`n=16, m=9`**; return in **88** steps at head **−86**.
- Start time **1,450,177**, input B/0 head **−779**, parameters **`n=368, m=28`**; return in **1,534** steps at head **−835**.

This census is reproducible and matches original-source machine semantics, but no finite replay is an all-time proof.

## Remaining decisive mathematical obligation

The auxiliary blank-root nonhalting gate is formalized as existence of a reachable D/0 configuration with immediate left `11` (see Agent42's `Root119Gate.blank_halts_iff_gate`). The existing `NoLeft4` shield and these four new closures do **not** establish an inductive classification of *all reachable B/0 section inputs*. Prior source-certified B-return families, especially the odd-even prefix and two-wave chains, have additional exact boundary hypotheses. The outstanding implication is that every *blank-reachable* nonhalting return belongs to some safely returning class, and that no intervening state reaches the gate. This requires a global word invariant or a complete symbolic return transition system, not further finite first-return percentages.

Highest-value direction: unify all certified B/0 families into a single set-of-patterns inductive closure theorem from the blank configuration, with the exposed odd-even boundary sentinel obligation and unbounded prefix-matching retained explicitly. A competing route is a direct global unreachable-gate invariant with fewer side-condition families. Both remain open.

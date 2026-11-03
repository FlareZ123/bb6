# Machine C mixed-modulus quotient: new experimental obstruction

**Agent 41, 2026-11-03. Research status: genuine original-source Lean-verified *transition soundness*; finite graph closure is NOT yet Lean-certified. BB(6) and Machine C remain open.** This dossier belongs in `im-results/`.

> **Source-soundness verification, 2026-11-03.** The [manual original-source Lean workflow 41680051185](https://github.com/FlareZ123/bb6/actions/runs/41680051185) completed **SUCCESS** at 17:01:42 UTC with original Agent11 `CLine.lean` unchanged, Lean 4.36.0-rc2, SHA256-checked source `Mixed96Sound.lean` (SHA256 `c8bdfe78aeb6ff10f3a4db22bb1b1504584bcbf1ca5fbb3f6ab1d6f5d83639f1`), and `Mixed96Bridge.lean`. The `nextC_source_equal` bridge has **no axioms**; `source_step_is_abstract_edge` and `source_reachable_is_closed` depend only on `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The finite BFS/certificate remains unverified in Lean, so the absence of `(13,31,0)` remains a **computational candidate** and yields **no original-source nonreachability theorem yet**.

## Question and candidate

For Agent11's authentic original-source accelerator `BB6CLine.nextC` (machine `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, blank-entry `(5,0,1)`), the Agent15 second necessary stopping family is
`(a,k,c)=(2*j+3,k,0)` with `k+j+3*m+5=2^(2*m+2)*(j+3)`.

A **new candidate** relative to previously explored power-of-two finite quotients arises when `j%96=5`, `m%96=29`: if the halting equation holds then `a%96=13`, `k%96=31`. The latter arithmetic statement is **fully checked in Lean** at [SecondMod96.lean](./SecondMod96.lean); compilation with Lean 4.36.0-rc2 gives only standard axioms `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The certificate does not establish that these target states are unreachable.

## Finite experiment

The deterministic independent C++ implementation [mixed96.cpp](./mixed96.cpp) uses the exact branch equations of Agent11's published `nextC` and the finite projection

`q_a(a)=a%96`, `q_k(k)=k%96`,
`q_c(c)=c` for `c<2`, else `2+(c-2)%48`.

At each abstract vertex, enumerate the two concrete representatives `x`, `x+M` of every coordinate at or above its base, form all Cartesian combinations, apply `nextC` and project the successor. From the projected blank entry `(5,0,1)`, exhaustive queue closure gives:

| Numerical measurement | Value |
|---|---:|
| Complete abstract universe | 460,800 |
| BFS-reached states | 260,672 |
| Edges processed from BFS-reached states | 2,022,544 |
| Reached status for `(13,31,0)` | absent |
| Reached status for `(29,79,0)` | absent |
| Reached status for `(61,79,0)` | absent |
| Reached status for `(77,31,0)` | absent |
| Absent second-family positions on 96×96 torus sampled at `j,m>=384` | 4,038 / 9,216 |

A separate Python implementation with separately transcribed `nextC`, quotient, and BFS agreed with these counts. In a larger **base-8 isotropic M96** quotient, independent C++/Python results were 1,124,864 vertices, 572,222 reached, 4,111,642 processed edges. Against the established B8/M1024 quotient, the isotropic M96 test had **660** pair positions absent in M96 but admitted in M1024 on a common `j,m mod3072` torus of sufficiently large parameters. This count is computational and includes overlaps with other formal results; no unconditional mathematical novelty is claimed. Comparing the reduced and original M96 models revealed 42 positions lost by the reduced model; the four displayed target cells remained excluded.

A complete Python scan of the reduced model's **abstract reverse edges** returned a 2,258-state full backward ancestor set for `(13,31,0)`, excluding the projected blank entry. The reverse adjacency included 3,575,808 edges over the entire graph. This compact *backward* certificate is a promising proof-generation route, still unverified by Lean.

## Trust boundary, next proof obligations

1. **Completed against unchanged source.** The definitionally equal acceleration and 96/96/48 mixed-quotient simulation have been proved for *all natural-number inputs*. The nontrivial phase-sensitive `c=0,1,2,3`, `a=0,1`, `k=0`, division by two, and boundary wraparound cases are all handled in [Mixed96Sound.lean.xz.b64](./Mixed96Sound.lean.xz.b64) and [Mixed96Bridge.lean](./Mixed96Bridge.lean). The compressed source expands to ordinary Lean text and is checksum-audited in CI.
2. Kernel-check the full finite set closure, preferably using the 2,258-state backward ancestor set and a small closure checker. The C++ output alone is untrusted computational evidence.
3. Compose source soundness + the checked graph + the checked stopping arithmetic + the Agent15 source-connected stopping/return bridge to derive an actual infinite family of forbidden halting parameters.
4. Audit against Agent15/38/43 and any independent prior art before promoting to `results/`.

Completed source proof: the full `qu_nextIf_rep`, `real_step_is_abstract_edge`, and actual-source `source_step_is_abstract_edge` and `source_reachable_is_closed` all kernel-check in the reproducible CI workflow. This proof supplies the required mathematically rigorous all-input quotient simulation. It intentionally does not smuggle in a finite BFS result.

## Reproduce

Build `mixed96.cpp` with a standards-conforming C++17 compiler and execute the program. It has no input dependencies. Expected first lines:

```text
BB6CLine mixed quotient (Ba,Bk,Bc)=(0,0,2), (Ma,Mk,Mc)=(96,96,48)
vertices=460800 reached=260672 successor_edges=2022544
projected (13,31,0) reached=0
```

For the Lean arithmetic module, use Lean 4.36.0-rc2 and compile `SecondMod96.lean` from this directory. It imports only `Std`. All computation and tests are reproducible without access to a presumed BB(6) solution.

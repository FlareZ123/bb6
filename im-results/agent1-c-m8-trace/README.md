# Machine C m=8 low gate: original-source kernel-verified all-time exclusion

**Agent 1, 2026-11-03. Current status (16:06 UTC):** The all-time m=8 certificate and the all-terminal-below-rank cutoff now **pass unchanged-original-source Lean 4.36.0-rc2 CI** in [manual run 41670233031](https://github.com/FlareZ123/bb6/actions/runs/41670233031), job 126036343299, against the real Agent46 first-return map, Agent3 strict mass theorem and Agent8 generic section engine. Its mathematical content existed in prior Agent1 local proofs; this run closes the original-source audit gap. Neither Machine C nor BB(6) is decided.

## Statement and exact proof strategy

Machine C's genuine blank-origin section begins at `(5,1)`. The genuine low halting gate at parameter `m=8` is `T=(1,524260)`, satisfying `524260+3*8+4=2^(2*8+3)`. This is exactly the target studied by Agent 34's 41-node reverse-cone computation, previously lacking a symbolic kernel closure proof (see [their dossier](../agent34-c-low-mod32/README.md)).

**Original-source kernel-checked theorem:** Under the original complete `bounce` and `exactSection` equations and their original source rank proof, there is **no natural section time `n`** at which the orbit of `(5,1)` reaches `(1,524260)`.

The exact *forward* section trace through return **150052** is replayed in the Lean kernel by 16 computational certificates, each covering up to 10,000 returns. The final authentic section state is `(621619,213453)`. The trace certificate proves *every* state at times `0≤n<150052` differs from `T`, plus equality of the return-150052 endpoint. Source theorem `section_mass_strict` proves each successful section strictly increases rank `a+2*k`. The endpoint has rank `1048525` and the gate has rank `1048521`. Therefore no later time can reach `T`, with no finite-horizon assumption.

**Stronger universal rank-cutoff theorem, original-source kernel checked:** For **all** natural counters `a,k`, if `secNext (a,k)=none` and `a+2*k<1048525`, then `(a,k)` is unreachable from the genuine blank section at **every** return time. This follows because any earlier terminal state would make the live return-150052 endpoint impossible, while any later state must have rank at least that endpoint. The local theorem `BB6Orig.all_terminal_below_rank_unreachable` has the same standard axiom audit. The source-connected `M8TraceCert.lean` contains the identically quantified `all_terminal_below_rank_unreachable` proof and passed original-source CI 41670233031. This supplies a reusable finite-rank cutoff for arbitrary immediate halting inputs without enumerating each target individually.

All local modules passed Lean 4.36.0-rc2 (the exact version pinned by the repository), with end theorem `BB6Orig.m8_gate_unreachable` reporting precisely `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, or additional declared axioms occur in the locally checked source-matching proof. Its exact source SHA256s:

| Local proof file | SHA256 |
|---|---|
| `ChainAllFix.lean` | `b84a086658f45ace96b2085c4772348bee170e5c3d03f485966bd43482c6a893` |
| `LocalM8Model.lean` | `3737f023c86fd7a81cdfd7b9ff52c763082188389683f8e201d029fcbc180bce` |
| `LocalM8Mass.lean` | `ff5654817d884190c034b05fb7dfdcbb5fc57be16f41ae7d5f86b09a5ab7a0df` |
| `LocalM8Result.lean` | `c760a0a1b61652c75b2c74038a1a8f13b8ff1790fd0e9ae1a83119e261421839` |

The local model reproduces exactly the branch equations of repository `im-results/agent46-c-jump/BounceCalc.lean` and `FastSectionDef.lean`, namespaced as `BB6Orig.bounceOrig` and `BB6Orig.exactSection`. The strict-rank proof is the original `im-results/agent3-c-bounce-inverse/SectionMassStrict.lean` proof with renamed symbols. The local Lean bridge `BB6Orig.next_eq` proves the computational evaluator and this well-founded copied definition are extensionally identical for *every* pair of naturals, using an all-input strong induction. The checked trace is separate from Agent34's Python inverse-graph computation and does not rely on its 41-node search or its six guard assumptions.

## Original-source connected files already committed

- [M8TraceBridge.lean](M8TraceBridge.lean): imports the genuine original `FastSectionDef` and `GenericSection`; proves total structural bounce evaluator equals original well-founded bounce, hence `fastNext = secNext` for all inputs. Provides verified segment checker soundness and its relation to the **original** section run.
- [M8TraceCert.lean](M8TraceCert.lean): exact 152 section checkpoints, 16 kernel `by decide` segment certificates, all-time proof via the original `SectionMassStrict`.
- Existing manual workflow [`agent3-c-bounce-inverse.yml`](../../.github/workflows/agent3-c-bounce-inverse.yml) now compiles both files after its unchanged source dependencies.

**Historical CI failure, now superseded by the successful source check 41670233031:** [run 41585354125](https://github.com/FlareZ123/bb6/actions/runs/41585354125) and [run 41585454294](https://github.com/FlareZ123/bb6/actions/runs/41585454294), including an attempted rerun, failed within four seconds with zero runner steps and no log artifact. The latest 10+ unrelated Agent22/35/39 workflows in this time period failed the same way. The 16:04–16:06 UTC successful run compiled both genuine-import modules and reported only `[propext, Classical.choice, Quot.sound]` for `m8_gate_unreachable` and `all_terminal_below_rank_unreachable`, with `[propext]` for the finite Boolean certificate. Runner failures in the cited earlier incidents had no proof-bearing steps and are now historical.

## Low stopping-family corollary, original-source certified (16:14 UTC)

[LowGatesOriginal.lean](LowGatesOriginal.lean) combines the source-certified general terminal-mass cutoff with exact evaluation of the nine low stopping input parameters

```
K(m) = 2^(2*m+3) - 3*m - 4,    0 ≤ m ≤ 8.
```

For **all** these m, `secNext (1,K(m))=none` and `1+2*K(m)<1048525`. It therefore proves, without any section-time cutoff,

```lean
BB6.Agent1M8.low_gates_0_through_8_unreachable
  (m : Nat) (hm : m ≤ 8) :
    ¬ ∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n
      (some (5,1)) = some (1, lowGate m)
```

Full unchanged-original-source [GitHub Actions 41671615685](https://github.com/FlareZ123/bb6/actions/runs/41671615685), job 126041181588, compiled all original dependencies and the new module. Final theorem axiom audit: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; the base gate arithmetic reports `[propext, Quot.sound]`. The initial [run 41671098998](https://github.com/FlareZ123/bb6/actions/runs/41671098998) failed because `decide` on imported `secNext` did not unfold; the corrected file rewrites through already proved `fastNext_eq_original` and was checked successfully. The nine-parameter corollary is implied by the existing general terminal cutoff; it does not establish nine independent new decisions or the rest of the infinite family.

## Remaining gap and implications

One member of the infinite Machine C low stopping family, together with all possible immediate stopping states of lower rank, is now excluded in the **authentic source-defined two-counter section map**. The separate source semantic bridge connecting this section to the raw Turing machine remains a dependency. This does **not** exclude `m=8+32t` uniformly, exclude any other unsolved stopping family, decide Machine C, or improve the global six-state Busy Beaver upper bound. Agent34's 41-node inverse-cone remains independently useful and unformalized. The reusable new technique is **structurally recursive evaluation with a proved source equivalence**, allowing a kernel-checked long forward trace plus a strict-rank cutoff. Original-source integration succeeded. Future work should test parameter-uniform generalization only where it materially helps the frontier.

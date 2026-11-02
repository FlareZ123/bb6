# Four rooted D-family holdouts: authenticated original-source to infinite-tape equivalence

**2026-11-02, Agent 19. Status: source-checked intermediate mathematical infrastructure.** This work makes machine-representation and first-halting-time transport exact. It does **not** decide any of the four rooted original Turing-machine halting questions, improve a BB(6) bound, or establish external novelty. Preserve it under `im-results/`, not `results/`.

## The gap being closed

Agent 3's `BB6.Portfolio` physically infinite tape is `Int → Bool`, with a `Fin 6` running state and an undefined transition represented by `Option.none`. Agent 31's original authenticated `CryptidBoundary` model uses finite nearest-first left/right Boolean lists with implicit zeros, an explicit state 6 as an absorbing halt, and a total primitive-step interpreter. Agent 32 proves that its list interpreter equals a generic list-tape semantics, with all padding and physical-tape laws authenticated. These representations cannot simply be substituted by `rfl` or assumed halting-equivalent.

The **literal D0 transition table** is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, parsed in Agent 3's `DParseRLE.lean`. This work imports those original modules **unmodified** in the final compilation.

## Formally proved interface

1. [PhysicalBridge.lean](./PhysicalBridge.lean) defines `tape`, `encode`, `SafeCfg`, `realize`, `stepFinite`, `runFinite`. A `SafeCfg` contains an arbitrary left/right finite-list tape and integer head offset, plus a proof of live state <6. `step_semiconjugacy` proves one-step exact preservation of all physical tape bits and head position, and `run_semiconjugacy` proves exact preservation for **every primitive time**. This includes `none` on an undefined transition, with no tape-window bound.
2. [SourceIntegration.lean](./SourceIntegration.lean) proves `list_step_projection` against **all 12 actual D0/source rule cases** and the original generic source's `goStay` frozen halt. The all-time `rel_run`, `source_total_halt_iff`, and `raw_run_none_iff_boundary_frozen` yield an exact relation at every natural time. `physical_halts_iff_boundary_halts` proves raw eventual halting iff the original source enters frozen state 6, for **every original list-tape initial configuration in a running state** and **any integer head offset**.
3. [UnaryBridge.lean](./UnaryBridge.lean) proves `unary_realize`, an exact equality of **all infinitely many physical tape bits** between Agent3's `F0Pure n 0` and Agent31's `CryptidBoundary.Cfg.mk [] false (List.replicate n true) 5` for **all n**. `unary_run_none_iff_source_frozen` and `unary_halts_iff_source_frozen` prove finite-time and eventual halt iff.
4. [RootTransfer.lean](./RootTransfer.lean) composes authenticated Agent3 literal-source-RLE parsing, mirror/relabel conjugacy, true blank-entry reductions and `unary_halts_iff_source_frozen` for **all six possible initial running states**, and separately the four externally listed rooted machine strings.
5. [ExactTime.lean](./ExactTime.lean) additionally proves the exact **first** halt-time iff using the source frozen state's first entry, rather than merely eventual halting. All four raw rooted machines have separately verified exact offsets from their authentic blank starts.
6. [CheckpointTransport.lean](./CheckpointTransport.lean) proves `source_live_checkpoint` for every original source proof of a finite exact run ending in a live state, and any initial integer physical head position. It supplies an integer witness for the final physical head and an **exact infinite-tape configuration equality** after the same number of primitive transitions. This strengthens the interface from halting predicates to arbitrary source-certified symbolic tape-return macros.

For a single source unary `U(n) := ⟨[],false, replicate n true,5⟩`, define `Frozen(n,t)` to mean `(CryptidBoundary.run t (U(n))).st = 6`. The actual formal conclusions are:

| Rooted machine literal | Pure unary source seed n | Raw successful prefix length a | Fully checked theorem |
| --- | ---: | ---: | --- |
| D0 `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` | 9 | 36 | `parsed_D0_root_source_iff`, `parsed_D0_exact_source_time` |
| D1 `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` | 39 | 403 | `parsed_D1_root_source_iff`, `parsed_D1_exact_source_time` |
| D2 `1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---` | 15 | 92 | `parsed_D2_root_source_iff`, `parsed_D2_exact_source_time` |
| D3 `1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---` | 5 | 15 | `parsed_D3_root_source_iff`, `parsed_D3_exact_source_time` |

Each existential theorem establishes: the actual blank-root raw machine halts iff `∃t, Frozen(n,t)`. Each exact theorem establishes, **for every t**: the original root halts after exactly `a+t` successful raw transitions iff `¬Frozen(n,t) ∧ Frozen(n,t+1)`. The distinction between a successful transition count and the first undefined halting call is explicit.

**This certifies four different source seeds. It is false to infer the four original blank outcomes agree merely because their transition tables are conjugate.** Nor does the quantified bridge prove that any of the four `Frozen` predicates is ever true or forever false.

## Reproduction and proof integrity

The manual-only [CI workflow](../../.github/workflows/agent19-d-physical.yml) restores unmodified Agent31 `Boundary.lean` from its compressed repository source using its existing SHA-256-checking `unpack.py`. It imports the original unchanged Agent3 `MachineConjugacy, DTableWitness, DStartFinite, DSectionTransfer, DAllStarts, DExactTimes, DParseRLE, DSourceCorollaries` and Agent32 `Generic, BoundaryPadding` modules. It then compiles the five new modules against those original definitions in Lean **4.36.0-rc2**.

- [CI 41468566128](https://github.com/FlareZ123/bb6/actions/runs/41468566128): initial `PhysicalBridge` success.
- [CI 41470155664](https://github.com/FlareZ123/bb6/actions/runs/41470155664): complete source-halt bridge success.
- [CI 41470482011](https://github.com/FlareZ123/bb6/actions/runs/41470482011): unary physical equality and halt iff success.
- [CI 41470742749](https://github.com/FlareZ123/bb6/actions/runs/41470742749): all six blank starts and four literal-rooted halting iff success.
- [CI 41471236744](https://github.com/FlareZ123/bb6/actions/runs/41471236744): exact first-halt-time RLE iff success.
- [CI 41472472908](https://github.com/FlareZ123/bb6/actions/runs/41472472908): arbitrary live source checkpoint to genuine physical raw infinite-tape checkpoint success, full unmodified source chain at commit `8956395540eb6be3beb9a2d0a952bb8f195bd51c`.

Source-level axiom audit for all final theorems printed only `[propext, Classical.choice, Quot.sound]` (or subsets). No `sorryAx`, `native_decide`, assumed cross-model equivalence, or untrusted simulator is used in the proof.

## Next mathematically decisive obligation

For each n in **{5,9,15,39}**, determine whether the **original source's** unary `U(n)` ever enters state 6. An all-time forward-invariant language or complete return-map argument handling the actual blank-reachable suffixes would be decisive; conditional family macros and finite traces alone cannot decide the infinite orbit. Existing source-authenticated Agent31/32/35/37 conditional symbolic returns can now be transported to any of the four genuine rooted machines, once their precise hypotheses are established for the particular returned tape.

This bridge supplies the previously missing formal representation and semantic compatibility; it remains an intermediate result until actual halting/nonhalting classification is achieved.

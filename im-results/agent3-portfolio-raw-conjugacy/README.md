# Source-certified raw-table conjugacy and four D-family blank starts

Status: **intermediate, not a Busy Beaver or holdout decision**. Agent 3, 2026-11-02.

## Why this matters

The pinned October 16 catalogue `resources/BB6_holdouts_663_2026-10-16.txt` contains multiple *rooted* BB(6) machines whose six-state transition tables are identical after a permutation of the six running states and possibly a left/right mirror. The **blank starting state changes under that permutation**. Proof transport must carry the start state; table-isomorphism alone does not identify blank-start halting outcomes.

`MachineConjugacy.lean` is a self-contained Lean 4.36.0-rc2 raw 2-symbol/6-state transition system with an infinite tape `Int → Bool`, arbitrary integer head position, and undefined-entry halting. It kernel-checks for **every transition table and every configuration**:

- `reflect_step`: reflection negates head position and mirrors every tape cell and movement direction;
- `rename_step`: a genuine six-state bijection transports one raw transition;
- `run_transport`: the conjugacy commutes with every finite raw run;
- `relabel_reflect_halts_iff`: exact halting equivalence when the initial state is mapped;
- `relabel_reflect_haltsAt_iff`: exact number `n` of successful transitions before an undefined entry is invariant.

The proofs require no external machine-specific formalization. In particular, reflection acts on the **whole tape** and not merely on transition letters.

## Fully certified D-family witness

`DTableWitness.lean` encodes all 12 raw table cells of each listed rooted machine literally. Kernel `decide` proves the exact finite table equality with explicit state permutations and a mirror. Writing states A..F as 0..5, the witnesses are:

| Root | Rooted RLE | D0-to-root state permutation | Mirror | Root blank A corresponds to D0 start |
| --- | --- | --- | --- | --- |
| D0 | `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` | identity | no | A |
| D1 | `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` | (D,E,C,F,B,A) | yes | F |
| D2 | `1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---` | (B,C,A,D,E,F) | yes | C |
| D3 | `1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---` | (C,A,B,E,D,F) | yes | B |

The three fully quantified Lean results, for every `n : Nat`, are

```lean
haltsAt D1 0 n ↔ haltsAt D0 5 n
haltsAt D2 0 n ↔ haltsAt D0 2 n
haltsAt D3 0 n ↔ haltsAt D0 1 n
```

and the corresponding three unbounded halting equivalences `D{1,2,3}_halts_from_blank`. These are *four distinct initial-state questions on a common table*. They do not prove that any of the four machines halt or never halt, and cannot establish BB(6).

## Evidence, reproduction and next use

Local verification: Linux Lean **4.36.0-rc2**, both original files compiled together under `LEAN_PATH=.`. The reported axioms of all three D time-of-halting theorems and general transform theorem were **only `[propext, Quot.sound]`**. No `sorryAx` or `native_decide`.

Manual-only CI: `.github/workflows/agent3-portfolio-raw-conjugacy.yml`. This respects the repository ban on per-commit CI.

The source is intentionally in `im-results/` since proof-of-isomorphism is an enabling infrastructure result, not an externally publishable BB(6) classification. Reuse this technique to transport existing D0 raw-TM macros **after** deriving the genuine blank-origin section for D0 starts B, C and F separately. Never assume a D0-start-A macro theorem applies to those starts without that bridge. The four-member grouping comes from the pinned snapshot and does not assert an up-to-date holdout count.

A remaining worthwhile extension is to specialize the theorem to the upstream `google-deepmind/cryptids` raw-machine semantics, proving the local definition agrees with their representation. Until then this is a kernel-checked mathematical theorem for precisely encoded raw Turing-machine rules with no direct source-level import from their code.

## Fully source-certified genuine blank-start unary sections

The extension `DStartFinite.lean` now constructs a finite-support exact raw simulator `FiniteCfg`, proves its complete all-time semantic equality `embed_step` and `embed_run` with the actual infinite `Int → Bool` D0 tape, and proves the exact unbounded identification of finite interval lists with the physical unary tape `F0Pure n h`. These source theorems justify three `decide`-checked finite blank-origin entry equalities **without any untrusted simulator-to-raw inference**:

| D0 initial blank state | Primitive raw steps | Exact endpoint | Rooted holdout |
| --- | ---: | --- | --- |
| B (state 1) | 15 | `F0Pure 5 (-3)` | D3 |
| C (state 2) | 92 | `F0Pure 15 (-12)` | D2 |
| F (state 5) | 403 | `F0Pure 39 (-35)` | D1 |

`F0Pure n h` has state F scanning a zero at physical tape position h, an **entirely blank infinite left half-tape**, exactly n consecutive ones immediately to the right, and an **entirely blank infinite suffix**. No finite-list trailing-zero convention is left implicit.

`DSectionTransfer.lean` strengthens these finite entries to genuine **all-time halting biconditionals**, using the generic partial-run prefix-cutoff theorem `haltsCfg_after_prefix`, a universal integer-head/tape translation conjugacy `translate_step`, and already certified state renaming/reflection:

```lean
D3_root_halts_iff_I5 :
  haltsFrom D3 0 ↔ HaltsCfg D0 (F0Pure 5 0)
D2_root_halts_iff_I15 :
  haltsFrom D2 0 ↔ HaltsCfg D0 (F0Pure 15 0)
D1_root_halts_iff_I39 :
  haltsFrom D1 0 ↔ HaltsCfg D0 (F0Pure 39 0)
```

All three are actual original-blank-root halting iff statements, allowing future research on the D0 F-section accelerator from **three additional authentic starts** n=5,15,39. Each right-side question remains open. They do **not** imply the three roots share the same halting outcome: the unary seeds are different.

The exact **unmodified full-source check**, including both new Lean files and independently regenerated 663-row ledger, passed [manual CI run 41460859283](https://github.com/FlareZ123/bb6/actions/runs/41460859283). The compiler reports only `[propext, Classical.choice, Quot.sound]` for each final original-root iff theorem; no `sorryAx`, `native_decide`, or other nonstandard theorem. The existing Agent31/35 D0 F-section results and their source-level macro proofs can now be studied as shared mechanisms across all four genuine rooted blank origins.

*Boundary:* This is complete original-source certification in our self-contained D0 raw-TM model; it has not been imported directly against the separate Agent31 `CryptidBoundary.Cfg` semantic representation. The unary configuration agrees with its declared physical meaning, but any additional direct composition with Agent31's theorems still needs an explicit same-tape representation bridge.


## Complete six-state blank-origin classification into four unary seeds

`DAllStarts.lean` proves a **single quantified original-source theorem for all six possible designated blank initial states** `s : Fin 6`. It is not restricted to the four roots already selected by the October 16 snapshot. The exact kernel-certified entry schedule is:

| D0 initial state | Raw steps | F0 unary length | Physical head |
| --- | ---: | ---: | ---: |
| A | 36 | 9 | -6 |
| B | 15 | 5 | -3 |
| C | 92 | 15 | -12 |
| D | 15 | 5 | -3 |
| E | 93 | 15 | -13 |
| F | 403 | 39 | -35 |

`every_blank_reaches_unary s` proves this exact physical-tape equality for **every** `s`, using the authenticated finite-support simulator semantics and kernel `decide` over the complete `Fin 6` enumeration. `every_blank_halts_iff_unary s` proves for **every** `s` the genuine all-time iff with `HaltsCfg D0 (F0Pure (startSeed s) 0)`.

Consequently, any *designated-state* version of the D0 table, under permitted renaming and left/right reflection, reduces to one of **four unary seeds: n=5,9,15,39**. The previously listed **four rooted holdouts map to four different seeds**, so this argument alone does not merge any two of those four open blank-halting questions. It additionally proves true same-table B-vs-D and C-vs-E blank-halting equivalences, since those pairs share the same seeds, without claiming the externally catalogued roots include the D/E starts. Source and CI evidence: [DAllStarts.lean](./DAllStarts.lean), [manual run 41461461590](https://github.com/FlareZ123/bb6/actions/runs/41461461590), final theorem axioms standard only.

`DExactTimes.lean` further proves the uniform exact-primitive-step iff

```lean
∀ (s : State) (n : Nat),
  haltsAt D0 s (startTime s + n) ↔
    HaltsAtCfg D0 (F0Pure (startSeed s) 0) n
```

and specializes to the three rooted RLEs with offsets **15, 92, and 403**. This is about equality of halting-time *predicates* under source-certified deterministic reduction. It gives no halting bound, because none of the four unary seeds is decided here.


## Whole-trajectory merges and literal-source end-to-end checks

An additional source theorem goes beyond same-halting-outcome for the unrooted D table. [DBlankFusion.lean](./DBlankFusion.lean) proves that the **actual, distinct blank starts B and D** have **identical complete physical configurations after 15 raw steps**; for every natural n, their configurations at step 15+n are equal. For **blank starts C and E**, the configurations at steps 92+n and 93+n agree under a physical translation of the full head/tape by one cell. Their exact primitive halting-time predicates inherit the corresponding zero-step and one-step offsets. This is a bona fide all-time coalescence, not only a finite common symbolic pattern. Original source and the 663-row ledger passed [Lean CI 41464911525](https://github.com/FlareZ123/bb6/actions/runs/41464911525), with only standard axioms.

[DParseRLE.lean](./DParseRLE.lean) checks the actual source data used for the four rooted machines by defining a decoder for all 12 transitions of the six-underscore-separated three-character notation and then kernel proving equality to all four literal D0-D3 definitions. [DSourceCorollaries.lean](./DSourceCorollaries.lean) imports those literal decoder equalities and proves the exact unbounded blank-halting iff and exact primitive-step-time iff of the three additional rooted RLEs from the *decoded text itself*. This guards against accidental mismatch between a named Lean table and the catalogued machine string; it does not assert any outcome for those open roots. All source checks passed the same manual CI.


## Second rooted table-family witness: S/T Cryptid

The general machinery now also applies to an unrelated two-root family in the October 16 pinned holdout snapshot. [STableWitness.lean](./STableWitness.lean) decodes both complete original RLE strings (the S/T pair already studied in Agent9), kernel proves their exact transition-table equality under a state permutation and physical left/right mirror, and proves both exact statements:

```lean
haltsFrom TTable 0 ↔ haltsFrom STable 1
∀ n, haltsAt TTable 0 n ↔ haltsAt STable 1 n
```

Here original `STable` is `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`, and `TTable` is `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`. The permutation from S to T is `(C,A,B,F,D,E)` on original A..F and the full physical tape is mirrored; the T-root blank A is the S-table blank **B**, while the listed S-root is original blank **A**. The new equivalence does **not** settle either rooted holdout or prove their blank orbits equivalent. It shows the reusable original-source state-dependent proof transport and provides an explicit interface for Agent9's genuine S/T initial-state analysis. This is an intermediate proof infrastructure result.

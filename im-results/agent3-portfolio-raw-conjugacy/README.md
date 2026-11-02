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


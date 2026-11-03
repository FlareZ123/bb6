# Agent 37: exact original D-family infinite-tape / finite-zipper bridge

**Status (2026-11-03): original-source Lean audit pending. Local Lean 4.36.0-rc2 proofs passed. Intermediate research, not a BB(6) root decision or new bound.**

## Scientific question

Agent3's [raw portfolio](../agent3-portfolio-raw-conjugacy/README.md) supplies a genuinely infinite, physical `Int → Bool` tape and proves all six original blank initial states of the D0 table reach a pure unary F/0 physical section; the four historic rooted holdouts correspond to lengths **9,39,15,5**. Agent31's [cryptid boundary](../agent31-cryptid-boundary/README.md) proves quantified primitive-step word-return theorems in a finite-list zipper representation with *implicit blank cells on both sides*. Agent37's previous [CrossModelBridge](../agent37-cryptid-model-bridge/CrossModelBridge.lean) compares two *finite-list* formalisms, not Agent3's actual infinite-tape configurations. This repository therefore lacked an explicit all-time semantic identification of those physical unary states with the finite-list representation used for symbolic proofs.

## New exact Lean proof structure

1. **`RawBoundaryBridge.lean` (restored source SHA256 `fd2e8553d8efcd662208e231d5e12b2fd8efce9f78d6a6ff9ffc4c001df54892`):** `tapeZ` interprets nearest-first finite left/right lists and the scanned bit as an entire physical two-sided tape at arbitrary integer head `p`. `tapeZ_goR` and `tapeZ_goL` establish full function equalities under both moves for *arbitrary left/right lists*, including implicit zeros. `pack` maps live zipper configurations with state less than 6 to the raw physical configuration, and maps the frozen halt state 6 to `Option.none`. `step_pack` verifies the literal eleven active D0 table branches and its undefined F/1 entry. `run_pack` proves for **all** `n : Nat`, all zipper configurations and all integer physical head positions that the **actual primitive-step** partial raw execution equals the packed `n`-step zipper execution, at the exactly updated physical head coordinate. `pack_unary` proves that `⟨[],false,List.replicate n true,5⟩` is **exactly** Agent3's `F0Pure n p` on the infinite physical tape, for every `n,p`.
2. **`RawBoundaryHalt.lean` (restored source SHA256 `9e931dc1726f209fa3e5b3bd5f65c17b59c02fde282ecb090fe42a6691605ac1`):** `raw_none_iff_halts` proves equivalence of existential `Option.none` and the existing `HaltsCfg` predicate. `boundary_step_bounded` and `boundary_run_bounded` ensure the actual unary start cannot enter arbitrary invalid states above 6. Then `raw_unary_halts_iff` proves, for **every n**, the original physical infinite-tape D0 unary configuration halts if and only if some original finite-list run from `unary n` enters frozen state 6. This handles the one-attempt difference between `Option.none` and a frozen-state model explicitly; there is no artificial step-count assertion.
3. **`RawBoundaryInit.lean`:** `unary_eq_init_replicate` is the zero-axiom identity `unary (k+2) = CryptidBoundary.init (List.replicate k true)`; `raw_init_halts_iff` composes this with the exact original physical tape halting iff, for **all k**.
4. **`RawBoundaryRoots.lean`:** short compositions with preexisting Agent3 proofs `every_blank_halts_iff_unary`, `D1_root_halts_iff_I39`, `D2_root_halts_iff_I15`, `D3_root_halts_iff_I5` yield the four literal original-root halting questions *directly in Agent31's actual `init` semantics*:
   - D0 blank A ↔ `∃ t, (CryptidBoundary.run t (CryptidBoundary.init (List.replicate 7 true))).st = 6`
   - D1 blank A ↔ the same with `37` true bits after the first two
   - D2 blank A ↔ the same with `13` true bits after the first two
   - D3 blank A ↔ the same with `3` true bits after the first two

The general `all_six_blank_states_halt_iff_zipper` composition also covers each designated original D0 start, without silently transferring between inequivalent rooted initial states.

## New 2026-11-03 physical-zero quotient and infinite raw return family

[RawBoundaryPhysicalQuotient.lean](./RawBoundaryPhysicalQuotient.lean) is a plain, locally kernel-verified fifth module. It proves that one explicitly stored trailing zero is mathematically identical to an implicit zero in the *full physical* tape (`pack_right_append_zero`). The general `physical_run_congruence` then states any two zipper presentations whose packed physical raw configuration is equal have equal packed trajectories at **every** primitive step, including halted ones. This removes a subtle but essential obstacle: Agent31's `full_B` theorem assumes a literal zero following the unary ones, whereas a pure blank-tail physical unary tape stores none.

For **every `k : Nat`**, `raw_full_B_physical` proves without finite enumeration:

```lean
∃ p : Int,
  BB6.Portfolio.run D0 (12*k*k+49*k+40)
    (some (BB6.Portfolio.F0Pure (3*k+2) 0)) =
      some (BB6.Portfolio.F0Pure (8*k+9) p)
```

The exact primitive transition count comes from the *unchanged source* `CryptidBoundary.full_B k []`, and the existential integer `p` is the physically correct head coordinate tracked by the bridge (Agent31 intentionally omits it). The proof is **locally kernel-checked with only `[propext, Classical.choice, Quot.sound]`**, and the manual original-source CI workflow includes this fifth module. This is an all-parameter original-physical-model transfer of a previously known zipper macro, and does not itself prove halting/nonhalting or a new BB(6) bound.

## Exact physical head displacement as a certified crossing-count identity

New [RawBoundarySpan source archive](./RawBoundarySpan.lean.xz.b64) (decoded Lean SHA256 `c0cf527d7bb5eb219a21f659fa811555e4618c8b08c2b9fdcd9221d65d5245b1`) extends the physical return proof from an existential head to a precise **all-parameter crossing-count equation**. The checksum-locked `unpack.py` now restores this source alongside the other two archived proofs. The local 4.36.0-rc2 kernel audit passes for every new theorem, with only `[propext, Classical.choice, Quot.sound]`; `full_B_head_crossings` uses only `[propext, Quot.sound]`.

For a list-based configuration `c` scanned physically at coordinate `p`, define its right boundary `rightEdge c p = p + c.r.length`. `crossesRight c=1` precisely when a live A/0 or B/1 right transition occurs with **empty** right list; it is zero otherwise. `rightCrossings n c` counts those events along the first `n` true machine transitions. The source theorem `rightEdge_run_exact` proves for **every n and every live endpoint** that the physical right boundary grows by **exactly** `rightCrossings n c`. The proof handles frozen-state 6 explicitly to prevent phantom posthalt head movements.

Consequently `raw_full_B_head_crossings k` proves for all natural k that the actual raw D0 tape's exact B-return has endpoint `F0Pure (8*k+9) p` at primitive time `12*k*k+49*k+40` with

```text
p = -(5*k+6) + rightCrossings (12*k*k+49*k+40)
      (CryptidBoundary.init (List.replicate (3*k) true ++ [false]))
```

The new `raw_full_B_head_lower` theorem thus certifies `p≥-(5*k+6)` universally. For inspected finite k=0..14, direct original D0 simulation found zero right-boundary crossings and `p=-(5*k+6)`. **This equality is conjectural for all k.** Its exact remaining proof obligation is the universally quantified zero-crossing theorem for the authentic `full_B` run. The crossing identity is a meaningful quantified boundary refinement but does not decide any rooted D machine or BB(6).

**CI status:** The updated existing manually dispatched Agent3 workflow compiles the full original source and all six bridge modules, including this restored span source, using original `Boundary.lean`. Earlier attempted original-source runs [41599582774](https://github.com/FlareZ123/bb6/actions/runs/41599582774) and [41602206015](https://github.com/FlareZ123/bb6/actions/runs/41602206015) both failed within seconds with unavailable job logs. Local proof compilation passed, but final full original-source verification remains pending; do not claim CI success.

## Verification status and reproducibility

The three archived sources use checksum-verifying atomic restoration under a file lock via [`unpack.py`](./unpack.py), and the unchanged Agent31 `Boundary.lean` separately restores at original SHA256 `0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883`.

Locally verified against Lean **4.36.0-rc2** with the actual checksum-verified `Boundary.lean`, and **definitionally identical minimal excerpts** of the original Agent3 `MachineConjugacy` raw step, `DTableWitness` D0 table, `DStartFinite` F0Pure and `DSectionTransfer` halting predicates. The complete local kernel checks of `step_pack`, `run_pack`, `pack_unary`, `raw_unary_halts_iff` and `raw_init_halts_iff` print only `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, mock theorem or additional postulate is used. The `unary_eq_init_replicate` theorem prints **no axioms**. Local checks used actual copied definitions but did **not** rebuild all full original Agent3 modules, so the final original-dependency certification is deliberately separate.

The existing manual [Agent3 original-source CI workflow](../../.github/workflows/agent3-portfolio-raw-conjugacy.yml) now restores and compiles **the entire original Agent3 chain** (including `DAllStarts`), original Agent31 `Boundary.lean`, and the new four proof modules, printing the final theorem axioms. **The first requested run [41599582774](https://github.com/FlareZ123/bb6/actions/runs/41599582774) was unsuccessful after approximately four seconds; both jobs failed and logs returned 404 before any useful compiler diagnostic. This is explicitly *not* a passing original-source verification.** Do not promote the direct `RawBoundaryRoots` source status without a successful rerun once runners work. If CI compiler errors emerge, reconcile them without weakening the original dependency chain.

## Use and limitations

The bridge removes an **exact model-identification gap** from Agent3's raw blank-start results to Agent31's symbolic return lemmas; it does not solve the remaining infinite iteration of the return map, prove any D0/D1/D2/D3 root halts or never halts, or improve the known Busy Beaver lower/upper bounds. It belongs in `im-results/` until a distinct genuinely novel mathematical conclusion justifies promotion.

Next research use: verify the full-source composition and then apply Agent31/Agent37 strict return and exceptional-word macro theorems to the four *authentic* unary seeds without confusing a physical F/0 return with a merely syntactic F state. Preserve original primitive-step offsets when attaching certificates to rooted blanks, and pursue a root-specific infinite-horizon invariant or counterexample rather than accumulating isolated finite cylinders.

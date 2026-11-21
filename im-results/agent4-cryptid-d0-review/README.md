# Raw TM62-to-D0 coordinate audit

**Status:** locally kernel-checked semantic preflight. This is not yet the final imported Mathlib bridge, and it is not a new blank-root halting theorem.

## Conclusion

The proposed absolute-coordinate map has the correct sign and orientation:

`absTape(T,h)(i) = decodeSymbol (T.nth (i-h))`.

For an external right move, Mathlib gives `(T.move Dir.right).nth i = T.nth (i+1)`; taking `h' = h+1` preserves the absolute cell coordinate. For a left move, `(T.move Dir.left).nth i = T.nth (i-1)`; taking `h' = h-1` does the same. The external TM writes before moving, and `Tape.write_nth` shows that only the old head cell changes. Thus the new absolute tape is exactly `updateTape absTape h (decodeSymbol w)`.

The checked file proves, for the exact eleven live transitions and F/1 halt case:

- `table_conjugate`: the external A–F / S0–S1 table maps to the repository's six-state D0 table;
- `absTape_write_move`: the coordinate equation for both directions and the write-before-move convention;
- `absStep_commute`: the one-step commuting square, including `none` at F/1;
- `run_transport`: finite runs commute at the **same n**;
- `haltsAt_transport`: exact-`n` halting is preserved in both directions;
- `halts_transport`: existential halting is preserved;
- `absCfg_AEmptyAt`: the abstract A(n,[]) section maps to the D0 pure-unary F-section at the same absolute head coordinate.

The exact-time transport does not add a step in the six-state D0 semantics. The extra +1 applies only if the terminal F/1 configuration is represented by the separate frozen sink state in CryptidBoundary.

## What is still needed for the actual upstream source

The checked model uses a relative tape observation `Int → ExtSymbol`. The actual external source uses `Turing.Tape Symbol`. The remaining adapter is small and is directly supported by the pinned Mathlib lemmas:

- `Tape.write_nth`: observation of `T.write w` is `relWrite (observe T) w`;
- `Tape.move_left_nth`: observation after a left move is `relMove .left`;
- `Tape.move_right_nth`: observation after a right move is `relMove .right`.

Here `observe T i := T.nth i`. The external `TM.step` writes the new symbol and then calls `Tape.move`, so the adapter must preserve that order. The external `A(n,[])` definition should then be shown to have relative observation `j ↦ if 0 < j ∧ j ≤ n then S1 else S0`, using the ListBlank nth/append lemmas. Do not describe the current file as having compiled those Mathlib adapter lemmas.

## Reproducible pins

The original source citation in the Agent32 bridge note is:

- proofs commit `1929f57df4dd7afcc11c3f458e20526fd1f991e0` (2025-08-23), Lean `4.22.0-rc4`, Mathlib `713ead03620c1f6965f94050048e50e8d1878872`, original theorem-file blob `3bdada95ae94bd1198c16bb3d32dfe724c59579c`.

The CI-compatible upstream snapshot already used by the repository's manual workflow is:

- proofs commit `b77dda5c79fb196d67ce35669e172ad632401c1b` (2026-10-20), Lean `4.36.0-rc1`;
- Mathlib commit `dfbc15ea6605db241da9cfd0632bbaf69b67e513`;
- theorem-file blob `973efd0efef1a415b58c49930d1f1a3233c75f49`;
- Mathlib Tape file blob `87c9df7aea22fe00eba77d179cc8449e6e04ac9d`.

I compared the external TM table, A definition, `reach_9_nil`, and the full `halts_A_mod_3_pow_108` declaration/proof between the two source snapshots: those extracted sections are byte-for-byte identical. The Mathlib 4.36 snapshot retains the same `Tape.move_left_nth`, `Tape.move_right_nth`, and `Tape.write_nth` statements, under the moved path `Mathlib/Computability/TuringMachine/Tape.lean`. Prefer the b77/dfbc15 snapshot for the repository's Lean 4.36 CI reproduction; the old 1929/713ead source is not the compatible CI pin.

## Local check and axiom profile

Compiled locally with Lean 4.36.0-rc2 using:

```sh
lean im-results/agent4-cryptid-d0-review/HeadRelativeFunctionAudit.lean
```

The printed axiom profiles contain no `sorryAx`. The checked transport theorems depend only on the standard `propext` and quotient soundness machinery; the section equality additionally reports `Classical.choice` from the local arithmetic/decision procedure. This is an abstract semantic preflight, not an axiom audit of the full upstream proof.

## Scope boundary

The upstream theorem proves halting from `A(3^108*k + C, [])`, where `C = 1975700577069254261393123959451562008800234946348086`. It does not prove that the authentic blank orbit reaches this cylinder. The separate `reach_9_nil` result reaches `A(9,[])`; the authentic-root hit problem remains open. This audit only removes the raw-step semantic translation as a source of uncertainty.


---

## 2026-11-21: A-row first-return drafts and 13-step authentic-root shadow

The following work is intermediate and **not yet kernel-checked**.

### A-zero/A-one first-return draft

`AZeroOneFirstReturn.lean` attempts strict no-intermediate-F lemmas for:
- `AZeroSource.full_A_zero`, the canonical q=b=0 row;
- `AOneSource.full_A_one`, the q>0,b=0 row.

It composes `PrefixNoF.prefixA_positive_noF`, `BoundaryPadding.source_init_pad`, the exact A-zero/A-one short macros, and `A1100First.sweepD_noF`. If compiled, these are stronger than physical first-return. They may fill two cases in a complete DRegular first-return partition; this coverage still needs review.

### 13-step root shadow

`Root13Shadow.md` records a new exact-arithmetic shadow of the external halting-cylinder path. At authentic-root DRegular section index 31,777, the state is `L(a,0,0)` and:

- `a-C ≡ 3^13 (mod 3^14)`;
- `p=(a-C)/3^13 ≡205 (mod 2187));
- `a ≡2863782241 (mod 3^20));
- the first 13 external A_step2 branch/argument/suffix updates match;
- the paths diverge at macro 14 because the next input residues are 1 (root) and 2 (external).

The exact arithmetic is reproducible with `root13_shadow_check.py`; `root20_cylinder_screen.mjs` screens DRegular states and explicit reentry endpoints through the episode-20 arithmetic lookahead. It found no exact (3^{108})-cylinder hit in that finite model screen and a unique maximum (v_3(a-C)=13) at index 31,777. It does not scan every primitive configuration inside exceptional packets.

`Root13Section.lean` is a source-anchor draft: it extracts the 4,484-step prefix of the already source-certified fifth reentry seed, then attempts to use `Agent25RootChain.extend_regular` to prove the blank root reaches the index-31,777 section. It also attempts the exact modular fingerprint and ten-step link to the sixth exceptional endpoint. This file is **uncompiled**.

The main remaining task is to compile `Root13Section.lean` and formalize the raw A_step2 replay of calls 11–13 (including the lifted K values) in Lean, then compose the raw-machine/CryptidBoundary conjugacy. Call 11 is already covered by `BlankSixthExceptional.first_nonregular_original` and `Agent32EAll.all_e_double_implicit_blank`. The numeric sweep parameters for the lifted root need not equal the external trace's small arguments; the general macro must be instantiated with the correct lifted unary length. This is not a BB(6) solution or a proof of nonhalting.


**Scope correction (11:40 UTC):** the arithmetic script verifies the affine parameter recurrence for the external offset sequence, but it does not independently execute the raw A_step2 macros on the lifted root. Only the first ten DRegular updates are currently backed by `DRegularShift.run_shift` (in the uncompiled `Root13Section.lean` draft). The claimed matching suffixes and branch/offset updates for calls 11–13 are conditional on proving that the general A_step2 source macro applies to the lifted q=4,b=1 suffix with its correct lifted sweep parameter. Do not describe the full 13-step path as source-established until that proof is composed.


**11th-update source match (11:49 UTC):** the external trace's step-11 suffix `0 1^8 0 1^6` is exactly the q=3 output of `Agent32EAll.all_e_double_implicit_blank`. The authentic root's `BlankSixthExceptional.first_nonregular_original` already invokes that theorem with its lifted parameter `k_root=3*t6+1`. Thus the source-macro gap is narrowed to updates 12–13, while the first-ten root-section affine composition remains in the uncompiled `Root13Section.lean` draft.


**Raw replay upgrade (11:47 UTC):** `root13_raw_macro_shadow.py` now runs the same sparse raw-machine `replay_macro` used by `cryptid_A_step2_replay.py` on the lifted root parameter after its first ten DRegular transitions. It verifies that calls 11–13 use the same arguments (35, 21, 5), branches, and output suffixes as the external trace, with output-difference valuations 2, 1, 0. This upgrades the 13-step shadow from a conditional affine prediction to exact simulator replay; it remains unformalized in Lean.

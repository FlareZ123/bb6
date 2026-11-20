# Raw TM62-to-D0 transport for Cryptid D

**Status (20 November 2026):** a concrete Mathlib-facing adapter draft now exists at [TM62MathlibD0Adapter.lean](./TM62MathlibD0Adapter.lean). It is not yet compiled against the exact upstream/Mathlib dependency closure, and no repository theorem or new halting result is claimed. Keep this dossier under `im-results/`; it does not establish blank-root reachability.

## The useful simplification

The pinned external proof does not need to be translated through the eleven-row `DRegular` return grammar. Its `A_step2` tactic proves ordinary finite runs of the raw six-state TM62. The entire 107-call path, including every arbitrary suffix, is already covered by that source proof. A single raw-step conjugacy to the repository's exact six-state model transfers the whole path at once.

External source:
- `int-y1/proofs`, commit `b77dda5c79fb196d67ce35669e172ad632401c1b` (the current source pin used by the adapter draft)
- `BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean`
- current upstream file: `BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean`

Repository model:
- `im-results/agent3-portfolio-raw-conjugacy/DTableWitness.lean`, definition `BB6.Portfolio.D0`
- `im-results/agent3-portfolio-raw-conjugacy/MachineConjugacy.lean`, especially `step`, `run`, and `run_transport`

## Exact transition-table comparison

Encode external states by
`A↦0, B↦1, C↦2, D↦3, E↦4, F↦5`,
and symbols by `S0↦false, S1↦true`.

The external TM62 table and `D0` agree on all eleven live entries:

| External | Read | Write | Move | Next |
|---|---:|---:|---|---:|
| A | 0 | 1 | R | B |
| A | 1 | 0 | R | E |
| B | 0 | 1 | L | C |
| B | 1 | 0 | R | A |
| C | 0 | 1 | L | A |
| C | 1 | 1 | L | D |
| D | 0 | 1 | L | C |
| D | 1 | 1 | L | F |
| E | 0 | 0 | L | C |
| E | 1 | 0 | L | B |
| F | 0 | 1 | L | E |

Both external TM62 and `D0` leave F/1 undefined. This is the exact standard six-state halting convention.

There is one separate encoding distinction: `CryptidBoundary`/ `BoundaryPadding.delta` represents F/1 by a transition to frozen state 6. Therefore:
- in the external TM62 and `D0` semantics, the machine halts at F/1 after its final live transition count (t);
- in `CryptidBoundary.run`, the same physical configuration takes one additional transition into state 6, so the corresponding frozen-state index is (t+1).

Do not conflate the `D0` exact six-state semantics with the seven-state sink encoding.

## A one-step transport that handles every suffix

The external proof uses Mathlib's `Turing.Tape Symbol`, whose `nth` coordinate is relative to the current head:
- `Tape.nth 0` is the scanned cell;
- positive indices are cells to the right;
- negative indices are cells to the left.

Use an absolute head coordinate (h:mathbb Z). Define the absolute tape represented by an external tape (T) as
[
  operatorname{absTape}(T,h)(i)
  = operatorname{decodeSymbol}(T.nth(i-h)).
]
Map an external configuration ((q,T)), together with (h), to
[
  operatorname{absCfg}(q,T,h)
  = langle operatorname{encodeState}(q), h,       operatorname{absTape}(T,h)angle
]
in `BB6.Portfolio.Cfg`.

The exact Mathlib lemmas used by the adapter draft are in the upstream project's pinned Mathlib revision `dfbc15ea6605db241da9cfd0632bbaf69b67e513`, `Mathlib/Computability/TuringMachine/Tape.lean`:
- `Tape.move_right_nth`: moving right changes relative coordinate (i) to old coordinate (i+1);
- `Tape.move_left_nth`: moving left changes relative coordinate (i) to old coordinate (i-1);
- `Tape.write_nth`: writing changes exactly relative coordinate zero.

Consequently:
1. If the external head moves right and (h' = h+1), then (operatorname{absTape}(T.move R,h')=operatorname{absTape}(T,h)).
2. If it moves left and (h' = h-1), the same equality holds.
3. Writing (w) before the move changes the absolute tape exactly by `updateTape absTape h (decodeSymbol w)`.
4. The state/symbol transition instruction is exactly `D0` by the table comparison above.

Thus the commuting equation is
[
  operatorname{absCfg}(operatorname{TM62.step}(q,T),h')
  = operatorname{D0.step}(operatorname{absCfg}(q,T,h))
]
whenever the external step is live, with the same `none` result on F/1. Package ((q,T,h)) as an extended external configuration so (h') is updated by the direction; then prove the finite-run theorem by induction. The existing `BB6.Portfolio.run_transport` is the right pattern for the induction.

This relation is over the *entire* infinite tape, so no finite suffix grammar, explicit blank padding convention, or terminal-zero normalization is needed. The external proof's arbitrary `ls` suffix is preserved automatically.

## Initial sections and the remaining open problem

The external definition is
`A(n,ls) := 0^∞ <F 1^n 0 ls 0^∞`.
Under `absCfg`, this is exactly the `D0` configuration with state F (index 5), head (h), scanned zero, and right-hand tape (1^n) followed by `ls`. In particular, `A(n,[])` maps to `BB6.Portfolio.F0Pure n h` from `DStartFinite.lean`.

The external `c₀` is the blank A-state start, which maps to `BB6.Portfolio.blank 0`. Its `reach_9_nil` is therefore compatible with the repository's already proved `DAllStarts.every_blank_reaches_unary` (for state 0, seed 9, head offset -6); the head offset is just the accumulated absolute coordinate, not a different tape.

Once the one-step transport is formalized, the external `halts_A_mod_3_pow_108` theorem transfers to the `D0` six-state semantics with no change in halting time. Its 107 `A_step2` macros and final halting tail transfer wholesale. If a result is instead stated through `CryptidBoundary`, account for the extra +1 sink transition described above.

**What this does not solve:** the external theorem proves that every
`A(3^108*k + C, [])` halts, with
`C = 1975700577069254261393123959451562008800234946348086`.
It does not prove that the authentic orbit from `A(9,[])` reaches this cylinder. The wiki's 2,728,570-state scan and closest 21/108 branch match are finite empirical evidence only. After the raw semantic transport, the decisive mathematical task is solely the authentic-root hit problem (or a genuine invariant excluding all certified halting classes), not another DRegular-to-A macro reconstruction.

## Acceptance boundary

## Concrete draft and validation boundary

`TM62MathlibD0Adapter.lean` now contains the state/symbol/direction encodings, exact table conjugacy, `Turing.Tape` absolute-coordinate observation, write-before-move lemma, extended configuration step, exact-n run transport, projection back to the external `stepNat`, and a conditional transfer of `halts_A_mod_3_pow_108` to `D0`'s `F0Pure` configurations. It also attempts the `A(n,[])` section identity by reducing `ListBlank.append_mk`/`nth_mk` to `List.getI` on `List.replicate`.

The generic Option-run projection and halting equivalence was separately compiled in Lean 4.36.0-rc2 in a scratch file. This checks the run/halts glue only; it does **not** compile the Mathlib-facing adapter. The local runtime now has Lean 4.36.0-rc2, but no Mathlib checkout/cache or upstream Lake project, so the exact dependency closure cannot be locally preflighted here. No CI run has been dispatched as a substitute. Agents 3 and 4 have been asked to review the exact source-level adapter, especially `A_tape_nth`, `stepNat`/`haltsIn` signatures, and the `Tape.write`/`Tape.move` composition.

Before treating this as a repository theorem, the exact file must compile against the pinned upstream/Mathlib closure, and its transitive `#print axioms D0_halts_on_A_cylinder` must be inspected. The table audit, generic scratch preflight, and source-level draft are not a kernel check of the concrete adapter.

# Agent 3 → Agent 4: pinned Mathlib Tape adapter details

I independently checked the **Lean 4.36-compatible** Mathlib source at commit `dfbc15ea6605db241da9cfd0632bbaf69b67e513`, file `Mathlib/Computability/TuringMachine/Tape.lean` (the path moved from the older 713ead snapshot).

The exact APIs used by your abstract audit are present:
- `Tape.nth` is head-relative: 0 -> head, n+1 -> right.nth n, and -(n+1) -> left.nth n.
- `Tape.move_left_nth`: `(T.move Dir.left).nth i = T.nth (i-1)`.
- `Tape.move_right_nth`: `(T.move Dir.right).nth i = T.nth (i+1)`.
- `Tape.write_nth`: `(T.write w).nth i = if i=0 then w else T.nth i`.
- `ListBlank.append_mk` and `ListBlank.nth_mk` are also available, alongside `Tape.mk'_nth_nat`.

A direct adapter can set `observe T i := T.nth i`. Extensionality plus the three Tape lemmas gives:
- `observe (T.write w) = relWrite (observe T) w`;
- `observe (T.move Dir.left T) = relMove .left (observe T)`;
- `observe (T.move Dir.right T) = relMove .right (observe T)`.

For the external section `A n [] = default <{{F}} [S1]^n +> [] +> default`, the right list reduces by `ListBlank.append_mk` to `ListBlank.mk (List.replicate n S1)`; `ListBlank.nth_mk` then reduces its nth value to `List.getI`. Splitting `Tape.nth` on negative, zero, and positive integers gives exactly:
`A_tape.nth j = S1 ↔ 0 < j ∧ j ≤ n`,
with S0 at the head and all negative coordinates. This is the `AEmptyAt n h` observation used in `HeadRelativeFunctionAudit.lean` (after shifting by h).

So the remaining Mathlib adapter is a small observational homomorphism; the abstract absolute-coordinate square and exact-n run transport in your file already have the right shape. The external `TM.step` in the b77 source still writes before moving, and `stepNat` iterates `Option.bind` exactly n times, so the transported `haltsAt` witness uses the same primitive n.

This is a source/API inspection only, not a compiled adapter. My local execution boundary is currently returning tool-level ClientErrors, so I have not claimed kernel verification.
— Agent 3

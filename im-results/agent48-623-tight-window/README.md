# Tighter #623 S-indexed reset window

**Status:** reproducible finite diagnostic and source-bound refinement; not an all-time #623 theorem.

## Mathematical refinement

The prior S-window envelope was

`B_old(ell)=max(34 ell+140, 36 ell+88)`.

Agent 1's exact weighted-correction formalization gives, for the drain statistics (D=L-2E), (E\le R\le L),

- `correction_buffer_closed`: `|C|,|F| ≤ 34L+122`;
- `one_extra_digit_carry_bound_closed`: the boundary carry quotient remains in `[-1,1]` even when the correction has magnitude exactly (K).

Since the mass depth gives (L\le\ell_S), the correction part needs only (34\ell_S+122), not (34\ell_S+140). Keep the existing centered-terminal bound (36\ell_S+88). This gives

[
B_{new}(\ell_S)=\max(34\ell_S+122,36\ell_S+88)\le B_{old}(\ell_S).
]

The exact references are:

- `im-results/agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.lean`, theorems `correction_buffer_closed` and `one_extra_digit_carry_bound_closed`;
- `im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitTransducerCarry.lean`, which proves the three-state digit transducer and exact weighted output statistics;
- `im-results/agent41-623-3euclidean/MonotoneMassWindow.md`, which proves (\ell_{S'}-\ell_S\in\{0,1\}) and the one-low/three-high window shift for the old envelope.

The same shift proof applies to (B_{new}): each affine term increases by at most 36 when `ell` increases by one, so (B'_{new}\le B_{new}+36). For (S\ge20), (\ell_S\ge3), hence (B_{new}\ge196) and (B'_{new}<3B_{new}). Therefore the same bounds (k'-k\in\{0,1\}), (j'-j\in\{0,1,2,3\}) follow. This is a paper derivation from the cited source lemmas, not a new Lean theorem in this directory.

## Finite diagnostic

Run from the repository root:

```sh
node im-results/agent48-623-tight-window/tight_mass_window_scan.js
```

The script uses the existing 263-state DFA at `im-results/agent32-623-phase-automaton/ResetPatternDFA.json` and the same explicit JavaScript transcription of the #623 high-level recurrence as `synchronizing_word_scan.js`. It recomputes the S-indexed windows for root indices 33 through 10,000 with both envelopes.

Observed output:

| Quantity | Old envelope | Tighter envelope |
| --- | ---: | ---: |
| States checked | 9,968 | 9,968 |
| DFA failures | 0 | 0 |
| Minimum word length | 8 | 7 |
| Maximum word length | 16 | 16 |
| First reset end | 3–12 | 3–12 |

More precisely:

- The low exponent (k) is unchanged on all 9,968 states.
- The high exponent (j) decreases by one only at indices 33, 34, and 35; it is unchanged at the other 9,965 states.
- The first-acceptance histogram is unchanged:
  `3:2196, 4:4210, 5:2241, 6:866, 7:290, 8:105, 9:37, 10:14, 11:6, 12:3`.
- The three shorter windows at indices 33–35 still accept by symbol 4.

The finite diagnostic therefore survives the sharper correction buffer and saves one high digit at the start of the proposed invariant. It does not prove that the reset DFA accepts every future S-window. The recurrence replay is computational, and no original-source root theorem or global BB(6) conclusion is claimed.

## Next useful use

Agent 32 can use (B_{new}) as the smaller S-window envelope when building the finite product-state closure. Preserve the full carry rectangles, source branch/sector, weighted drain interface, one-symbol low shift, and zero-to-three high extensions; the tighter buffer does not remove those obligations.

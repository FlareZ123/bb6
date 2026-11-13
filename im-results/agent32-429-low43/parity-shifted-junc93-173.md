# Parity-shifted continuation from J(93,0,173): simulation dossier

**Status: computational observation only; no Lean theorem currently connects this path.** This note corrects the earlier mistaken attempt to apply `low43_C0_record 86 3` directly at `J(93,0,173)`.

## Parameter mismatch

The formal low43 entry theorem starts from `jTape (v+2*k+2) (2*v+1)`. Junc canonicalization identifies `J(u,0,w)` with `jTape u w`. Thus `J(93,0,173)` would require (v=86) and (93=86+2k+2), i.e. (2k=5), impossible. The instance ((v,k)=(86,3)) is `jTape 94 173`, not `jTape 93 173`.

## Observed C/0 checkpoint

Using the original #429 transition table, simulation from `J(93,0,173)` reaches C/0 after 31,154 steps:
- state C, current symbol 0, head (+178);
- head range during this prefix: ([-176,178]);
- right neighbour is blank;
- the left word, nearest cell first, is
  `true :: false :: (ones 353 ++ pairs01 4 ++ [false] ++ ones 6)`.

This is a parity-shifted tail, not `low43_C0_zipper 86 3`.

For comparison, the standard input `J(94,0,173)` and the shifted input `J(93,0,173)` have identical state/head traces through step 31,154. Their initial tapes differ only at the far-left cells (-188,-193,-194), none of which is visited during the first 31,154 steps. The first visit to (-188) occurs at step 31,528; there the two paths read different symbols and diverge. The shifted path subsequently reaches `J(0,7,349)` at step 31,579 (425 steps after the C/0 checkpoint).

## Remaining 102,656-step continuation

From `J(0,7,349)`, the simulation reaches `J(0,0,408)` after 102,656 more steps. The observed checkpoint decomposition is:

| Start | End | Steps | Likely existing macro |
|---|---:|---:|---|
| J(0,7,349) | J(10,0,346) | 41 | `juncNormalize_delta` |
| J(10,0,346) | J(23,0,323) | 527 | `juncNormalize_delta` |
| J(23,0,323) | J(49,0,274) | 2,373 | `juncNormalize_delta` |
| J(49,0,274) | J(101,0,173) | 10,121 | `juncNormalize_delta` |
| J(101,0,173) | J(15,172,1) | 30,100 | positive iteration, N=86 |
| J(15,172,1) | J(0,15,349) | 1,551 | unresolved partial return |
| J(0,15,349) | J(18,0,346) | 57 | `juncNormalize_delta` |
| J(18,0,346) | J(39,0,307) | 1,503 | `juncNormalize_delta` |
| J(39,0,307) | J(81,0,226) | 6,501 | `juncNormalize_delta` |
| J(81,0,226) | J(165,0,61) | 27,081 | `juncNormalize_delta` |
| J(165,0,61) | J(135,60,1) | 3,780 | positive iteration, N=30 |
| J(135,60,1) | J(0,135,125) | 1,735 | unresolved partial return |
| J(0,135,125) | J(138,0,122) | 297 | `juncNormalize_delta` |
| J(138,0,122) | J(78,120,2) | 14,760 | positive iteration, N=60 |
| J(78,120,2) | J(0,0,408) | 2,229 | unresolved partial return |

The 15 durations sum to 102,656. Including the preceding 425-step C/0-to-`J(0,7,349)` leg, the complete C/0 continuation is 103,081 steps. The three positive iterations satisfy (2Nle w). The nine normalization legs appear to be direct instances of the existing normalization theorem. The three partial returns are the main unresolved subproblems.

## Research implications

- The 31,154-step entry needs a parity-shifted variant of the low43 physical record. The far-left tail is the only difference between the standard and shifted input during the initial prefix; a lower head bound plus a tape-modification invariance lemma may transfer the common prefix.
- The shifted C/0 continuation has a simple observed 425-step endpoint `J(0,7,349)`.
- The 102,656-step path after `J(0,7,349)` is mostly existing normalization and positive-iteration macros. Focus formal work on the three partial returns from `J(15,172,1)`, `J(135,60,1)`, and `J(78,120,2)`.
- The full observed interval from `J(0,344)` to `J(0,408)` is 145,374 steps: 11,139 to `J(93,0,173)`, then 134,235 to `J(0,0,408)`. It remains a simulation observation until every link is formally proved.

The direct simulation used the standard six-state table:
`A: 1RB/0LF; B: 1RC/1RA; C: 0RD/0RB; D: 1LE/halt; E: 0LA/1LE; F: 1RD/1LA`.

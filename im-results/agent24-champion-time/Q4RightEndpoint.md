# q4 suffix right-facing endpoint lemma

**Status: uncompiled proof candidate; not a BB(6) result.**

The source q4 prefix theorem is kernel-checked for every odd bounded inner counter and arbitrary parameters:
`Agent6Q4Prefix.oddRst2_q4_prefix` reaches state 4 at the original head after `32+12*a` moves, with the complete left-facing word and a finite right-shape contract. Its current public contract gives only five trailing blank cells.

The q4 suffix frame has origin
`g = h+10+3*b` and final head `g-5 = h+5+3*b`. Its final local frame marks exactly
`[-3,-2,-1,2,3,4]` relative to g. Therefore, viewed rightward from the final head, its first nine cells are

`[0,1,1,1,0,0,1,1,1]`,

which is exactly `s0RightFacing 0`.

For every cell beyond those nine, the suffix preserves the input tape: such a cell lies beyond `g+4`, outside the final frame; `d0Sweep_after` reduces it to the first-ten-frame tape; the first-ten frame preserves cells at or beyond `h+10). The q4 prefix's full right-facing stream, if exported, gives the required blank tail because `q4RightFacing b` has length `9+3*b).

## Lean interface

`Q4RightEndpoint.lean` contains:

- `q4_prefix_far_tail`: turns the proposed full right-stream equality from Agent 6 into an all-cells blank-tail fact.
- `q4_suffix_right_word`: from the q4 suffix frame and that blank-tail fact, proves pointwise equality of the entire final right-facing stream with `s0RightFacing 0`.

The prefix theorem now exports its internal `hrightT` proof as the additional result conjunct
`∀ i, Tq (h+1+i) = sideBit (q4RightFacing b) i`
in commit `7369e2778204ed876a9cb8529981ac1f09ad9796`. This is already proved inside the prefix theorem and is stronger than its finite `q4RightShape` contract, but the strengthened theorem signature still awaits CI compilation.

The helper is included after `Q4Suffix.lean` in the existing manual-only champion-root audit. It now also contains `q4_suffix_run_right_word`, which composes the suffix's exact `run tm2 (39+3*b)` frame theorem with the pointwise right-facing endpoint lemma. No push trigger or new workflow was created. The local shell is unavailable in this invocation, and no workflow-dispatch action is exposed; consequently this file has **not** been compiled. The latest champion-root workflow run is failed, and the available job-step summary does not identify the failing Lean module.

## Remaining proof obligations

1. Compile the strengthened prefix theorem and this helper under Lean 4.36.0-rc2.
2. Prove the corresponding left-facing endpoint equality. The expected word is
   `d0pow b ++ d1pow 2 ++ (q4LeftFacing L (n-1) a).drop 1`,
   matching the source target's left-facing S1 encoding. The coordinate split is now explicit: for `i<3*b`, the queried cell is `x_i=h+5+3*b-i`; when `x_i≥h+10`, write `x_i-(h+10)=3*j+r` and use `d0Sweep_block` (the residue `r=2` is equivalent to `i%3=2`); when `x_i<h+10`, only offsets `h+6` through `h+9` remain and the first-ten frame gives `1,0,0,1`. The next six cells are `h+5` through `h`, all marked, and for `i≥3*b+6` the tape is unchanged at `h-1-j`, so the prefix left-stream equality supplies the remaining tail. The helper lemmas `q4Endpoint_d0pow_length`, `q4Endpoint_sideBit_d0pow_mod`, and `q4Endpoint_sideBit_drop_one` are now in the Lean module to support this proof.
3. Combine both half-tape equalities with the frame's state/head fields to identify the complete output with
   `s1Config L (n-1) 1 (a+b+2) (2^b-1) 0 (h+5+3*b)`.
4. Compose the exact prefix and suffix runs. Until these obligations are kernel-checked, the proposed `71+12*a+3*b` Rst2 cost remains conditional.

The finite q4 screens are documented separately in [LCIncQ4Cut.md](LCIncQ4Cut.md); they are empirical support, not substitutes for the quantified source proof.

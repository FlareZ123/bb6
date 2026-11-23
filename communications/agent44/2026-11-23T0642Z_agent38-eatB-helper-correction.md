# Agent 38 → Agent 44: correction — eatB2/eatB12R are distinct from eatC2/eatC12

Correction to my previous helper-inventory message: I conflated the B- and C-side eat functions. The pinned source definitions show they use different literal blocks:

- `eatC2`: `[run1, run0, run1]`; `eatB2`: `[run0, run1, run1]`.
- `eatC12`: `[run1, run0, run1, run0, run1]`; `eatB12R`: `[run0, run1, run0, run1, run1]`.

Thus the existing `eatC2_num_sum_le` / `eatC12_num_sum_le` do **not** discharge the BB sweep's `eatB2` / `eatB12R` obligations. Your original note is right: instantiate `eatFuel_num_sum_le` separately with the B-side blocks, using `getRep2_num` / `getRep12_num`. The `stepElemBB_length_le` gap I identified remains. Sorry for the false correction.

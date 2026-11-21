# S1 carry-output bridge: local proof repair

## Failure reproduced

The exact `m1-even-valuation-source.yml` workflow run `44910559991` stopped in `im-results/agent24-champion-time/S1CarryOutputBridge.lean`. The relevant failures were:

1. The `sideBit_d0pow_formula` recurrence used `omega` on `i-3) and a modulo expression without first exposing the subtraction identity.
2. The proof of `∃ i : Nat, x = -(i:Int)` asked `omega` to synthesize an unbounded Nat witness from `x≤0`.
3. Four `simp` steps made no progress because `sideBit_append` selected the final suffix append, not the leading `d0pow r` / `d1pow r) block whose length was needed.

## Repair applied

The source file now:

- derives (3\le i\) from `¬ i < 3` using `Nat.le_of_not_gt`, then obtains `i=(i-3)+3` with `Nat.sub_add_cancel`;
- proves the bound recurrence by `Nat.add_lt_add_iff_right` after `Nat.mul_succ`, and lets simplification handle the modulo-(3) recurrence;
- constructs the Nat index directly as `Int.toNat (-x)`, justified by `Int.neg_nonneg` and `Int.toNat_of_nonneg`;
- normalizes append associativity before `sideBit_append`, so the rewrite exposes the leading counter block and its length.

## Local verification

Lean 4.36.0-rc2 compiled the patched `S1CarryOutputBridge.lean` against interface-equivalent local stubs for `CountedSuffixOutput` and `CountedCarryLeftOutput`; the declarations used from those modules were copied from their current source. The axiom profiles are:

- `d0pow_length`: `[propext, Quot.sound]`;
- `sideBit_d0pow_formula`: `[propext, Quot.sound]`;
- `s1Config_decrement_leftOutput`: `[propext, Classical.choice, Quot.sound]`.

No `sorryAx` remains in the repaired declarations. The remaining `Classical.choice` is proof-only and is not a placeholder.

**Boundary:** this local preflight does not replace compilation against the exact repository imports. The M1 source workflow must be rerun after this commit; if it passes, the next gate is the broader `middle34-acceptance` workflow. Do not treat the local stub compilation as full closure acceptance.

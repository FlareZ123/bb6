# Extracting primitive-time bounds from the Cryptids RLE halting proofs

**Status:** new intermediate method; not yet formalized or accepted. This note records a concrete cost semantics for the upstream RLE engine and the proof obligations needed to turn its `IsHalt` certificates into local `DecidedBelow` leaves.

## Why the existing halting transfer is insufficient

At upstream commit `3647718b5df22e1a61462dec0376bd204526285a`, the exact-overlap modules prove `IsHalt target` by using `BusyBeaver.Calculi.HaltShared`. The inspected F289 module

`BusyBeaver/BB6/Halt/M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.lean`

builds an RLE-stack proof and ends with `reach_0 : StateHalts target_tm ckpt0`, then transfers that to `IsHalt target`.

The gap is precise. In `HaltShared.lean`:

- `CanHalt M c := ∃ cfg, (c [M]⊢* cfg) ∧ (step M cfg).isNone`;
- `StateHalts` and `rleStep_halts` preserve this existential `ReflTransGen` reachability;
- `runBatches_halts` proves that 380 batches of the RLE engine preserve halting, but does not record how many primitive Turing steps the induced `ReflTransGen` path contains.

The local frontier predicate is stricter:

`DecidedBelow B m := NeverHalts m ∨ ∃ n, n+1 ≤ B ∧ HaltsAfter m n`.

Thus an `IsHalt` transfer alone cannot be inserted into `DecidedBelow B). The missing object is a primitive-step upper bound, not another proof that the machine halts.

## Concrete RLE workload in the inspected proof

The upstream engine defines:

- `runStepsInner 25`: at most 25 calls to `rleStep`;
- `runBatches b`: `b` repetitions of `runStepsInner 25`.

The inspected module proves the deterministic checkpoint equalities:

- `runBatches 100 ckpt0 = ckpt5`;
- `runBatches 100 ckpt5 = ckpt10`;
- `runBatches 100 ckpt10 = ckpt15`;
- `runBatches 80 ckpt15` is halted.

So the certificate performs exactly 380 batches, i.e. at most **9,500 RLE transitions**. These are not 9,500 TM steps: one RLE transition may contract a variable-length primitive path.

## Primitive costs already exposed by the source rules

The `execute n` tactic in `HaltShared.lean` iterates the primitive `step` tactic exactly `n` times. The basic rule costs are therefore source-readable:

| Rule | Primitive steps |
|---|---:|
| `B_nil`, `BR_nil`, `C_nil` | 1 |
| `B_zero`, `DR0_zero` | 4 |
| `B_succ` | 2 |
| `BR_zero` | 2 |
| `BR_one` | 4 |
| `BR_add_two` | 5 |
| `DR0_nil`, `DR0_succ` | 3 |
| `C_zero_nil` | 3 |
| `C_zero_zero` | 5 |
| `C_zero_one` | 17 |
| `C_zero_add_two` | 4 |
| `C_one_nil` | 5 |
| `C_one_zero` | 7 |
| `C_one_succ` | 6 |
| `C_add_two_halt` | 3 |

Several reusable cost recurrences follow by adding the primitive costs in the corresponding `stepStar_trans` proofs. Let

`S(segs) = Σ_{(r,c)∈segs} c(6r+30)`.

The fixed composite rules satisfy:
- `rule_C_bot_four(bot)`: `4bot+12`;
- `rule_DR0_bot(k)`: `6k+14`;
- `rule_BR_blkR_one(r)`: `2r+15`.

The clean-mode recurrences then give the following exact costs or safe upper bounds:

1. `rule_C_one_prefix(c)` costs at most `4c+10`; hence `rule_C_r_add_three(r)` costs at most `4r+15`, and `rule_C_blkL_pow(c,r)` costs at most `c(4r+15)`.
2. `rule_BR_blkR_clean(c,r)` costs `c(2r+15)`.
3. `clean_sweep_core(segs,bot)` costs `6bot+41+S(segs)`: the empty-segment case is `rule_C_bot_four(bot)` followed by `rule_DR0_bot(0)` and `rule_BR_blkR_one(bot)`, and each segment `(r,c)` contributes `c(6r+30)`.
4. `clean_DR0_one(c0,segs,bot)` costs `6c0+6bot+46+S(segs)`.
5. `clean_DR0_zeros(q,c0,segs,bot)` costs
   `6q(c0+bot)+15q²+41q+qS(segs)`.
6. `clean_RNIL_one(c0,segs,bot)` costs at most `6c0+6bot+61+S(segs)`.
7. `clean_RNIL_zero_pow(q,segs,bot)` costs at most
   `6q bot+18q²+49q+qS(segs)`; the `30i` increase in `S` from each `pushSeg 0 1` is included.
8. `clean_P1_one(r,segs,bot)` costs at most `10r+6bot+75+S(segs)`.
9. `clean_P1_pow(q,r,segs,bot)` costs at most
   `q(10r+6bot+6q+75+S(segs)) +(6r+42)q(q-1)/2`.
10. `clean_P2_one(r,segs,bot)` is bounded by
    `15r²+6r bot+113r+12bot+165+(r+2)S(segs)`.
11. Consequently `clean_P2_pow(q,r,segs,bot)` is bounded by
    `q(15r²+113r+165)`
    `+(6r+12)(q bot +(r+1)q(q+1)/2)`
    `+(r+2)(qS(segs)+(24r+48)q(q-1)/2)`.
12. The same source inductions give `rule_DR0_bot_zeros(q,k) = 6kq+9q²+9q`: sum `rule_DR0_bot(k+3i)` and `rule_BR_one` for `i=0,…,q-1`.

These formulas are obtained directly from the displayed inductions in `HaltShared.lean`: `clean_DR0_zeros`, `clean_RNIL_zero_pow`, `clean_P1_pow`, and `clean_P2_pow` repeatedly call their one-block lemmas while increasing the packed segment weight. In particular, simply multiplying the one-block cost by `q` is not sound unless the growth of `S(segs)` is included. The resulting summation identities were cross-checked with deterministic BigInt arithmetic over `q≤5`, `c0≤3`, `bot≤4`, `S≤7`, and `r≤4` (11,520 comparisons, no mismatches); the reproducible checker is [check_cost_formulas.js](check_cost_formulas.js). This is an algebraic sanity check only, not a proof of the Lean rule costs or the RLE soundness theorem.

### Dispatch-level bounds

Let `M` bound every numeric field in the current RLE state, and let `L` bound the number of packed segments. The dispatch code and rule costs above give these coarse bounds (the clean P2 branch is dominant):

- raw B: at most `4M+4`;
- raw BR: at most `M(2M+15)+5`, from `rule_BR_blkR_succ`;
- raw DR0: at most `15M²+9M`, from `rule_DR0_bot_zeros`;
- raw C: at most `M(4M+15)+17`, from `rule_C_blkL_pow`;
- clean BR: at most `M(2M+15)`;
- clean DR0: bounded by `clean_DR0_zeros` with `q,c0,bot≤M`;
- clean B: bounded by the larger of `clean_P1_pow` and `clean_P2_pow`;
- clean C and successful `tryPack`: zero primitive cost because they only change the RLE representation.

For `M=2^128` and `L=2^15`, `S(segs)≤L·M·(6M+30)<2^274`. The clean P2 recurrence is then below `2^540` per RLE transition; the raw branches and other clean branches are lower-order. This gives a target total below `2^554` over 9,500 transitions, so `2^640` is a deliberately loose candidate bound. This remains conditional on a kernel-checked invariant for **all intermediate states**, not merely the four checkpoints, and on formal cost-indexed soundness for every dispatch branch.

## Cost-indexed engine that would close the gap

Add a parallel cost semantics rather than trying to extract a number from a `ReflTransGen` proof in `Prop`:

1. Define `rleStepCost : RleFullState → Nat` by matching the same cases as `rleStep`.
   - A successful `tryPack` is zero primitive cost because `tryPack_spec` proves denotational equality.
   - The clean-`C` unpack branch is also zero cost because it changes representation only.
   - Raw branches use the fixed and zero-run costs above.
   - Clean branches use the recurrences above.
2. Prove a cost-indexed soundness theorem for each branch, ideally as an equality for `multiStep` or a Type-valued trace, not merely `ReflTransGen`.
3. Define `runStepsInnerCost` and `runBatchesCost` to accumulate the costs alongside the existing deterministic state updates. For the inspected proof the total is the sum over 9,500 `rleStepCost` calls.
4. Prove that the final accumulated cost gives a `HaltsAfter` witness for the exact RLE target, then transfer through the existing `isHalt_toBB_iff_halts` bridge and the local literal-table equality.
5. Compare the resulting bound with the champion score and package a `DecidedBelow championBound` leaf.

A direct function from the existing `ReflTransGen` proof to a Nat is not available: `ReflTransGen` is a proposition and proof irrelevance erases its witness length. A separate cost-indexed semantics is the correct interface.

## Coarse-bound strategy (conjectural until proved)

The checkpoint literals in the inspected F289 proof have numeric fields below roughly `2^73`; that observation alone does **not** bound intermediate RLE states. A future source proof should expose every intermediate state in the 9,500-step deterministic trace and kernel-check a bound such as:

- every numeric counter in every intermediate `RleFullState` is below `2^128`;
- the number of packed segments is below `2^15).

Under those two hypotheses, `S(segs) < 2^274). The displayed clean-mode recurrences then put the dominant `clean_P2_pow` branch below about `2^540) primitive steps per RLE transition; 9,500 transitions remain below a conservative `2^640` total. This is only a sizing calculation: raw-branch bounds, all branch maxima, the intermediate-state invariant, and the exact soundness theorem still need proof. Do not publish `2^640` as a bound until those obligations are formalized and checked.

If the cost-indexed proof is successful, the resulting bound is negligible compared with the TM63 champion lower-bound expression, so the machine can be discharged as a `DecidedBelow` leaf without needing its exact decimal halting time. The same generic cost engine should then transfer to the other upstream `IsHalt` modules using `HaltShared`.

## Compatibility and acceptance constraints

The current pinned local Cryptids source does not contain `BusyBeaver/Calculi/HaltShared.lean` or `BusyBeaver/Calculi/Counter.lean`. The proof modules are present at upstream commit `3647718b5df22e1a61462dec0376bd204526285a`, whose upstream toolchain is Lean 4.35.0-rc4; the BB6 project requires local Lean 4.36.0-rc2. Do not change the shared dependency pin or claim a local theorem from the upstream source without a separate exact-version preflight.

The clean next experiment is a scratch Lake project pinned to that upstream commit, with the cost semantics added there and the local RC2 toolchain selected. If local runtime is unavailable, preserve this as an intermediate method note; do not dispatch CI as a substitute for local preflight.

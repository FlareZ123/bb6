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

So the first F289 certificate performs exactly 380 batches, i.e. at most **9,500 RLE transitions**. These are not 9,500 TM steps: one RLE transition may contract a variable-length primitive path.

The second live F289 root,
`M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH`,
uses five 120-batch chunks and a final 140-batch chunk: 740 batches, or at most **18,500 RLE transitions**. Its checkpoint chain is `ckpt0 → ckpt6 → ckpt12 → ckpt18 → ckpt24 → ckpt30 → halted`.

## Primitive costs already exposed by the source rules

The inspected F289 module's `HasRleStackRules` instance defines `execute n` by iterating its primitive `step` tactic exactly `n` times; the basic rule costs below are read from those `execute n` invocations. `HaltShared.lean` supplies the RLE dispatch and clean-mode inductions whose composite costs are obtained by summing those primitive rule costs: the `step` tactic applies the one-step-to-plus lemma once, then `finish` closes the reflexive tail with `multiStep_zero`.

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
- raw BR: at most `M(2M+15)+5`, from `rule_BR_blkR_succ` plus the fixed atomic cases;
- raw DR0: at most `15M²+9M+4`, from `rule_DR0_bot_zeros` plus the fixed atomic cases;
- raw C: at most `M(4M+15)+17`, from `rule_C_blkL_pow` plus the fixed atomic cases;
- clean BR: at most `M(2M+15)+5`, covering both the block rule and all atomic cases;
- clean DR0: the maximum of `clean_DR0_one` and `clean_DR0_zeros` with `q,c0,bot≤M`;
- clean B: the maximum of the RNIL composition, `clean_P1_pow`, `clean_P2_pow`, and the fixed `4M+4` zero-run/atomic cases;
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

A direct function from the existing `ReflTransGen` proof to a Nat is not available: `ReflTransGen` is a proposition and proof irrelevance erases its witness length. A separate cost-indexed semantics is the correct interface. The pinned upstream `BusyBeaver/Basic.lean` already provides the right exact-step API: `multiStep M c n`, `multiStep_trans`, `multiStep_succ`, and `multiStep_eq_none_of_isNone`. Define a proposition such as `ReachWithin M c c' B := ∃ n, n ≤ B ∧ multiStep M c n = some c'`, and prove its additive transitivity with `multiStep_trans`. Each primitive `rule_*` should have a parallel bounded/exact certificate built from its `execute n` body; do not attempt to recover the length by eliminating the existing `StepPlus`/`ReflTransGen` proof after the fact.

## First end-to-end F289 accumulator run (computational candidate)

A JavaScript/BigInt port of the upstream state transitions was run from `ckpt0`. This applies only to the rooted RLE `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---` (the first F289 row in `upstream-exact-overlap.tsv`); the local ledger reuses family label F289 for a different RLE as well, which is **not** covered by this run. The second F289 row's module uses the **same 19 named primitive rule costs** and the same shared RLE engine, but starts at `ckpt0 = ⟨.C, .raw [], [.z 1], false⟩` and uses five 120-batch chunks plus a final 140-batch chunk (at most 18,500 RLE transitions). A first CI attempt exposed a validator bug: the old script compared raw source-order `execute n` lists against the class-field order, although the theorem-name-to-cost mapping was identical. The script now audits each `rule_*` theorem by name, treats `rule_BR_nil` as the `rule_B_nil` alias, and separately checks the one-step `init_reaches_stack` cost. The corrected replay succeeded in [CI run 45180798535](https://github.com/FlareZ123/bb6/actions/runs/45180798535), matched all five intermediate checkpoints, and ended halted. It reproduced the Lean proof's three explicit checkpoints **exactly**: `runBatches 100 ckpt0 = ckpt5`, the next 100 batches equal `ckpt10`, and the next 100 equal `ckpt15`. The final 80-batch run reached `halted = true`. This validates the state-update port against the proof's checkpoint literals; it does not prove the primitive cost semantics. The full state simulator and branch-cost accumulator are preserved in [simulate_f289_rle.js](simulate_f289_rle.js); run it with Node against the exact upstream F289 proof module (commit `3647718b5df22e1a61462dec0376bd204526285a`).

Accumulating the branch-specific bounds above over the at-most 9,500 RLE transitions (the loop stops calling `rleStep` once the halted flag is set) gave:

- first 100 batches: `153233965714336055848900074`;
- second 100 batches: `21420259195008061453530364129891259`;
- third 100 batches: `124842490278774511382713615548623788982769809`;
- final 80 batches: `1003323861768105046986224874806868631470122277577`.

The sum is the **RLE-transition cost sum**
`N = 1003448704258405241756955830449585121679083838719 < 2^160`.
The source proof also takes one primitive step in `init_reaches_stack` before `ckpt0), so the complete primitive-step candidate is `N+1 = 1003448704258405241756955830449585121679083838720`. Since `2^160 = 1461501637330902918203684832716283019655932542976`, the strict `n+1≤B` requirement is still satisfied with slack `458052933072497676446729002266697897976848704256`.

This is a **computational candidate upper bound**, not yet a theorem. If every branch cost is shown sound against the primitive TM transition relation, the first F289 machine reaches its halting state in at most `N+1` primitive steps, including the initial source-to-stack transition. The bound is already far below the TM63 tower-scale lower-bound expression, so it would suffice for a `DecidedBelow` leaf once the cost soundness and exact table transfer are formalized. Do not add F289 to the certified frontier on the basis of this simulation alone.


## Second F289 end-to-end accumulator replay (computational candidate)

The corrected name-indexed script was run against the exact second F289 module at upstream commit `3647718b5df22e1a61462dec0376bd204526285a` in [CI run 45180798535](https://github.com/FlareZ123/bb6/actions/runs/45180798535). The run:
- parsed RLE `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH`;
- checked all 19 named primitive rule costs against the source theorems, including the `rule_BR_nil := rule_B_nil` alias;
- checked `init_reaches_stack` has exactly one primitive step;
- replayed all 18,500 RLE transitions through the five checkpoint literals `ckpt6`, `ckpt12`, `ckpt18`, `ckpt24`, and `ckpt30`;
- reached the final halted state.

The six chunk bounds were:
1. `1724680719097766021408040530663` (120 batches, `ckpt0 → ckpt6`);
2. `14039024050947366338187144312225222365474367` (120, `ckpt6 → ckpt12`);
3. `87449181964252787543177016957072539598502800356767` (120, `ckpt12 → ckpt18`);
4. `602268854723326478762652439723887760350363137223325183816` (120, `ckpt18 → ckpt24`);
5. `53342105669046226234904710261225146666525575497594622324027059833` (120, `ckpt24 → ckpt30`);
6. `126276899598505474034431441069542948364223497533749631986191720748701360` (140, `ckpt30 → halted`).

The RLE-transition cost sum is
`126276952940611745349599848496735249080302155982948794561796401307306806`.
Adding the one initial primitive step gives the candidate
`126276952940611745349599848496735249080302155982948794561796401307306807`,
which has 237 binary digits and is therefore strictly below `2^237`. This is **computational evidence only**: it validates the state replay and the name-indexed primitive cost table, not the branchwise theorem that each cost bounds the corresponding primitive TM path.


## Prefer an evaluated cost accumulator over a global invariant

The previous coarse argument's hardest obligation is proving `M≤2^128` and `L≤2^15` for every intermediate state. A better implementation is to evaluate a branch-specific cost bound alongside the actual deterministic run:

1. Define `rleStepBound(s)` by the same dispatch as `rleStep(s)`. It returns 0 for `tryPack` and clean-C representation changes; the raw branches return the relevant fixed/zero-run or block-run formula; the clean branches return the corresponding `clean_*_pow` or `clean_DR0_zeros` recurrence.
2. Define `runStepsInnerBound(n,s)` to return `(finalState,totalBound)`, adding `rleStepBound(s)` before recursing on `rleStep(s)`. Define `runBatchesBound` analogously, preserving the existing 25-step batch structure.
3. Prove a bounded-step relation for each branch, e.g. `∃ n ≤ rleStepBound(s), multiStep target_tm (evalRle s) n = some (evalRle (rleStep s))`. Compose these bounds additively through `runStepsInnerBound` and `runBatchesBound`.
4. At the final halted state, combine the bounded trace with `StateHalts` to obtain `HaltsAfter` at some `n≤runBatchesBound 380 ckpt0`.
5. Evaluate the concrete `runBatchesBound 380 ckpt0` with `native_decide` (or kernel reduction if tractable) and prove it is below the champion bound. This computes over the actual intermediate states, so no separate guessed maximum-counter invariant is required.

A useful proof shape is a bounded analogue of the existing `StateHalts` invariant: define `StateHaltsWithin(s,B) := ∃ cfg n, n≤B ∧ multiStep target_tm (evalRle s) n = some cfg ∧ step target_tm cfg = none`. Each `rleStep` branch proves a `ReachWithin` path from `evalRle s` to `evalRle (rleStep s)` with its branch bound. A bounded analogue of `stateHalts_of_stepStar` then propagates `StateHaltsWithin` backwards, adding bounds, and the final halted state starts with bound 0. This mirrors the current `rleStep_halts` proof and may be easier to formalize than a separate forward trace theorem.\n\nThis is the preferred route: the deterministic state path is already executable and checkpointed by the upstream proof. The only new proof burden is the branchwise cost soundness. The global `M,L` argument below is a fallback if evaluating the accumulator is too expensive. The exact transfer chain is already available on both sides. Upstream `BusyBeaver/Bridge.lean` proves `multiStep_toBB M c n`, identifying `BusyBeaver.multiStep M.toBB c.toBB n` with the `n`-fold iteration of `ConjectureMachines.step M`. Locally, `im-results/agent4-coverage-smoke/CryptidsHaltIff.lean` proves `BB6.ConjectureBridge.source_halts_after_iff_agent8_halts_after m n`, converting the exact source-run halt at `n` to `BB6Coverage.HaltsAfter (toAgent8 m) n`. Thus a bounded RLE trace plus the final no-successor fact can feed the existing `DecidedBelow` pipeline; no new absolute-tape adapter is needed.

## Coarse-bound strategy (conjectural until proved)

The checkpoint literals in the inspected F289 proof have numeric fields below roughly `2^73`; that observation alone does **not** bound intermediate RLE states. A future source proof should expose every intermediate state in the 9,500-step deterministic trace and kernel-check a bound such as:

- every numeric counter in every intermediate `RleFullState` is below `2^128`;
- the number of packed segments is below `2^15).

Under those two hypotheses, `S(segs) < 2^274). The displayed clean-mode recurrences then put the dominant `clean_P2_pow` branch below about `2^540) primitive steps per RLE transition; 9,500 transitions remain below a conservative `2^640` total. This is only a sizing calculation: raw-branch bounds, all branch maxima, the intermediate-state invariant, and the exact soundness theorem still need proof. Do not publish `2^640` as a bound until those obligations are formalized and checked.

If the cost-indexed proof is successful, the resulting bound is negligible compared with the TM63 champion lower-bound expression, so the machine can be discharged as a `DecidedBelow` leaf without needing its exact decimal halting time. The same generic cost engine should then transfer to the other upstream `IsHalt` modules using `HaltShared`.

## Compatibility and acceptance constraints

The current pinned local Cryptids source does not contain `BusyBeaver/Calculi/HaltShared.lean` or `BusyBeaver/Calculi/Counter.lean`. The proof modules are present at upstream commit `3647718b5df22e1a61462dec0376bd204526285a`, whose upstream toolchain is Lean 4.35.0-rc4; the BB6 project requires local Lean 4.36.0-rc2. Do not change the shared dependency pin or claim a local theorem from the upstream source without a separate exact-version preflight.

The clean next experiment is a scratch Lake project pinned to that upstream commit, with the cost semantics added there and the local RC2 toolchain selected. If local runtime is unavailable, preserve this as an intermediate method note; do not dispatch CI as a substitute for local preflight.

# Agent 38: sharpened Machine C finite-target time bounds

**Status:** source-verified *intermediate* mathematics. Does **not** establish halting/nonhalting of Machine C or solve BB(6). This refines the already source-certified rank/target bounds of Agent 42 and the quadratic progress work of Agent 8, who retain priority for those broader ideas.

## Exact source and theorem

Machine C `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` has published accelerator `BB6CLine.nextC`, blank entry `(5,0,1)` and a complete halting-gateway family `(0,2j,4j+10)` (Agent 11, source bridge Agent 21). Our CQuarter module copies the published transition function definitionally, and `CQuarterBridge.lean` proves by Lean kernel computation `source_next_agrees` to the **unmodified** `im-results/agent11-c-line/CLine.lean`.

Put `R(a,k,c)=a+2k+c`, `P(a,k,c)=a+c` and
`E(s)=R(s)(R(s)+1)-2P(s)`. For **every** successful accelerated transition `s→t`, the Lean theorem `energy_step` shows

`E(s)+4 ≤ E(t)`.

In particular, any length-n successful accelerator path ending at a target with rank R has `4n ≤ R(R+1)`. This is a universal source-level finite-target certificate, `source_hit_target_iff_quarter_bound`, even for arbitrary starting triples; no blank-specific assumption is needed.

## Stronger genuine blank-entry bound

Every live Machine C transition is rank-nondecreasing, and the initial rank is six. The stronger exact step inequality for all source states with `R(s)≥6` is

`E(s)+4R(t)+4 ≤ E(t)+4R(s)`.

This is `strong_step`; its telescope `strong_run` is valid along the complete blank-entry accelerated orbit. At `s=(5,0,1)` we have `R=6,E=30`. At the arbitrary thin gateway `t=(0,2j,4j+10)`, `R=8j+10,P=4j+10`. The stronger inequality yields the exact theorem

`blank_thin_cutoff_clean (j n : Nat): run n (some (5,0,1)) = some (0,2*j,4*j+10) → n ≤ 16*j*(j+2)+11`.

`source_blank_thin_cutoff_clean` transports precisely this statement to the unmodified original source via `source_run_agrees`. This is an all-j theorem with quantified n. It does **not** exclude any j or imply a uniform finite bound over all j.

### Prior work and improvement size

Agent 42's independent, source-verified sharp rank-level counting theorem `CThinCutoff.lean` already established that any first encounter with that gateway occurs before `(4j+6)^2` accelerator calls, hence `n≤16j²+48j+35`. Our bound is `n≤16j²+32j+11`, a **16j+24** reduction in the explicit safe bound for every j. Both bounds have the same quadratic leading term; the improvement is lower-order. Agent 8 independently developed earlier quadratic progress potentials. No claim of new publishable BB(6) frontier discovery is made.

## Reproduction and axiom audit

- `CQuarter.lean`: full exact accelerator copy, all-case global energy increment, telescoping, universal target bound.
- `CQuarterBridge.lean`: definitional equality to the original unmodified Agent 11 source and universal source transfer.
- `CBlankImproved.lean`: rank monotonicity, stronger all-rank-≥6 step, telescope, clean integer gateway-time bound.
- `CBlankBridge.lean`: exact import-based source transfer of the blank theorem.
- `.github/workflows/agent38-c-quarter.yml`: manually dispatched Lean 4.36.0-rc2 verification. There is deliberately no per-commit trigger.

Pinned full unmodified-source **successful** [CI run 41423202668](https://github.com/FlareZ123/bb6/actions/runs/41423202668), at commit `282c1f7d5d04d304668874c55b4d6fb4fd549df1`. Independent earlier verification [run 41422191594](https://github.com/FlareZ123/bb6/actions/runs/41422191594) checked the generic energy theorem; second successful [run 41423005414](https://github.com/FlareZ123/bb6/actions/runs/41423005414) checked the strong blank-only inequality before the cleaned corollary. The final Lean audit for all theorem statements reported only standard `[propext, Quot.sound]` or a subset, with no `sorryAx` or `admit`.

## What remains

All fixed j are decidable by source-verified finite simulation, but the set of potential j is infinite. Proving that **none** are reachable, or exhibiting a reachable j, is necessary to decide this one Machine C holdout. The energy argument alone cannot discharge this global obligation. It may be reused to reduce the finite search cost in formal proof certificates and targeted inverse reachability checks. Do not place this report under `results/` unless a genuinely publishable and externally validated consequence is discovered.

## Kernel-verified boundary witness on the true blank orbit

An attempted next strengthening of our potential argument would replace the
coefficient four in `E(s)+4R(t)+4 ≤ E(t)+4R(s)` by a larger constant,
hoping to improve the quadratic-bound coefficient. The actual blank orbit
**reaches** precisely the obstruction to doing this.

The theorem `BB6Agent38.blank_reaches_a2_c0` certifies
```lean
run 567323514 (some (5,0,1)) = some (2,62973,0)
```
against the exact Machine C `nextC`. The source-level `CJumpWitnessBridge.lean`
proves this statement using the unmodified original Agent 11 `CLine.lean`,
then derives the genuine inductive theorem
`BB6CLine.Reach (2,62973,0)`.
The very next published transition is
`(2,62973,0) → (0,1,125947)`.
On this edge rank increases by **one**, energy increases by **eight**, and the
coefficient-four inequality holds with **equality**. The theorem
`no_energy_slope_ge_five` therefore shows that for every coefficient
`lambda≥5`, the proposed strengthened progress inequality is **false even
when universally quantified only over blank-reachable source states**.

The certificate `CJumpCore.lean` proves the high-sector sweep shortcut by
induction, plus the exact `path_sound` theorem which equates its accumulated
step count to repeated original accelerated transitions. The 106 explicit
length-at-most-1024 shortcut blocks in `CJumpWitness.lean` each use Lean's
**kernel-reduced** `by decide`, and `run_add` composes them into one exact
567,323,514-transition equality. This certificate deliberately avoids
`native_decide`, trusted external computation, `sorry`, and unverified
simulation assumptions.

The shortcut trace contains **107,886** jump events and was cross-checked
independently with a completely unskipped C++ implementation of the original
accelerated map, which reproduces the checkpoint
`(62970,2,62971)` at exactly step **567,260,544** and the final state
`(2,62973,0)` at step **567,323,514**. Full original-source proof CI
[run 41425320997](https://github.com/FlareZ123/bb6/actions/runs/41425320997)
**passed**, including original Machine C source, the 106-block proof and
inductive reachability bridge, with standard Lean axioms only. The
subsequent added optimality corollary has an independent local Lean proof
and a separately dispatched CI check.

The finite witness is useful as a falsification of an attractive stronger
inequality. It gives no halting witness and implies no new BB(6) bound. The
first 567 million accelerated Machine C steps are already much shorter than
the previously explored numerical horizons of Agent 8; this is a *formal
reachability certificate* for one concrete intermediate milestone, rather
than a new simulation survival record.

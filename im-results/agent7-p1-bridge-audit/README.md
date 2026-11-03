# Agent 7 R006: full original-TM to sparse P1 halting criterion audit

Date: 2026-11-03. **Disposition: accept the precisely stated halting equivalence.**
The audit finds no source mismatch or missing semantic bridge in the existing original-machine theorem.
This is a validation report. It is not an original BB(6) decision or a new mathematical result.

## The exact source claim

For the pinned Cryptids root `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`,
`BB6.P1Bridge.raw_halts_iff_sparse_gate` states

```lean
IsHalt Source.target ↔
  ∃ n, ReachT 2 1 2 (14*2^n - 2*n - 10)
```

Here `ReachT` means zero or more actual defined accelerated `T` transitions, not a
synthetic backward-ancestor relation or arbitrary starting configuration.

The existing proof has the following complete dependency path:

1. The original [Cryptids source at commit ced8f9f](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean) defines the target using `load_rle_machine%` and proves `is_valid_highLevel_acceleration`, including genuine blank initialization. The P1 image uses all natural pairs, and its initial state is (2,1).
2. [The original `BusyBeaver.Defs`](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/Defs.lean) defines `IsValidAcceleration` with three obligations: `init_reaches`, positive-step `step_some`, and a terminal-configuration `step_none`. [Its `Basic` theorem](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/Basic.lean) proves `IsHalt M ↔ CollatzHalts next start`, both directions, using this structure.
3. [`P1Bridge.lean`](../agent19-p1-source-bridge/P1Bridge.lean) proves `G_agree` by strong induction for all `k,c`, and `T_agree` for all `a,c`. It transports the upstream certificate to the local `HaltingFunnel.T`, proving `raw_halts_iff` without a bridge hypothesis.
4. [`P1HaltingBridge.lean`](../agent19-p1-source-bridge/P1HaltingBridge.lean) matches local `HaltsIn` certificates to the exact `Option.bind` iteration in `CollatzHalts` in both directions. [`BlankCriterion.lean`](../agent4-halting-funnel/BlankCriterion.lean) independently proves finite local halting iff finite `ReachT` of the displayed infinite gate family, including the even-sector converse and odd-sector excursions.

## Original-source CI and change-drift check

[GitHub Actions run 41388451571](https://github.com/FlareZ123/bb6/actions/runs/41388451571/job/125094384626)
succeeded on 2026-11-02, commit `78c81ed96615523cc7989798442588dcfa3c2421`, pinned upstream commit `ced8f9f44f67a167d5ecc03e687b048c67926371`, Lean 4.35.0-rc4.

The job log directly reports the final theorem's axiom set as
`[propext, Classical.choice, Quot.sound]`. All five Agent4 dependency files, both
Agent19 bridge files, the harmless module-preparation script, and the manual
workflow have exactly the same Git blob SHA at CI commit and current `main`.
The preparation script only inserts the `module` declaration and import/section visibility.
No hidden synthetic substitution of the target table occurs.

## Independent finite raw-machine cross-check

Reproduce with [`raw_bridge_audit.py`](raw_bridge_audit.py). This independent
Python simulator parses the six-state RLE and maintains physical tape cells,
head position and machine state. It initializes each canonical P1 physical tape,
computes the published nested drain and `T` separately, and executes actual
Turing-machine transitions until the predicted encoded hub is reached or an
undefined transition is encountered.

- **1600 / 1600 synthetic configurations matched**, exhaustive a,c=0..39.
- Branch sample sizes: c=0: 40, c=1: 40, even-left: 760, halting gate: 20,
  odd-c=3 drain: 20, odd-c>=4 drain: 720.
- Largest finite raw segment: 1514 defined steps from P1(39,39).
- Six actual blank steps reach the exact physical hub P1(2,1).
- **100 further P1 macro transitions matched**, ending at (95,93), after
  112859 raw steps *including the initial six*.

The historical Agent1 checker reports 112669 raw steps for 100 hub transitions
**counting the blank-to-P1 initial transition as one**. Our count includes
100 P1 transitions **after** the initial six, hence one extra macro transition.
The 100th P1 transition consumes exactly 190 defined raw steps:
`112669 + 190 = 112859`. No disagreement remains.

An undefined transition is reported after a number of defined raw steps.
Finite raw tests are independent evidence for the interpretation, with no
universal coverage; the mathematical proof comes from Lean.

## Limits and disposition

This source-connected criterion is accepted as a faithful all-time equivalence
for the specified rooted original machine at the verified pinned revision.
No unknown `IsValidAcceleration` assumption remains in the final theorem.
Novelty of the bridge itself is an integration of already established published
and internal proofs. The still-unproved question is whether the actual orbit
can meet any target `(2,14*2^n-2*n-10)`. A proof excluding individual infinite
index classes does not settle all surviving indices. No BB(6) upper bound follows.

Next mathematically decisive task: produce a single all-index invariant or
decide a remaining genuine critical reset. Avoid rerunning the existing bridge
CI absent relevant source change or a real discrepancy.

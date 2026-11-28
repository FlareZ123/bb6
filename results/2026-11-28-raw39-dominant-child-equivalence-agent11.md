# Raw39 has exactly the same finite weighted-bound spectrum as its A1=1LE successor

**Result status:** full original-source Lean 4.36.0-rc2 proof accepted 28 November 2026, [CI run 46113180731](https://github.com/FlareZ123/bb6/actions/runs/46113180731), artifact [15250477247](https://github.com/FlareZ123/bb6/actions/runs/46113180731/artifacts/15250477247), SHA-256 `805df34b7a9ce8a1f0ae6c465f4186a4cbf25b56484f8fc4df7c5f7606185b55`. Source `../im-results/agent11-raw39/Raw39ThresholdReduction.lean`. Transitive axiom profiles for both new theorems: **only `propext`, `Classical.choice`, `Quot.sound`**. Original-source audit includes the ten accepted first-hole sibling modules, not assumptions masquerading as leaf proofs.

## Mathematical statement

Consider the partial six-state, two-symbol Turing machine

```text
P = 1RB---_1RC---_0RD---_1LD0RA_------_------
```

and its refinement `Q = refine P (A,1) (1LE)`, in the standard first-one normalization and weighted halting convention of `BB6Coverage`. A partial machine is `Bound B` if **every halting total compatible completion** has weighted halting cost at most natural number `B` (including blank-start initial delay and halt query).

**Theorem (all thresholds):** For every `B : Nat`,

```lean
BB6.Agent11Raw39ThresholdReduction.bound_iff_oneLE (B : Nat) :
  Bound B P ↔ Bound B Q
```

The equivalence is not conditional on a complete 1LE classification and does not claim that `Bound B Q` holds for any particular `B`. It proves that every possible **uniform finite bound**, if established for `Q`, is immediately a bound for the entire seven-hole cylinder `P` and conversely.

## Proof

1. **Necessity, every threshold.** Each completion of `Q` is a completion of `P`. Thus any bound for `P` applies to `Q` by `refine_preserves_compat`.
2. **Strictly dominant child witness.** A source-accepted specific 1LE completion has weighted halting cost exactly **28,311**. The theorem `BB6.Agent43Raw391LELate.parent_not_bound` formally excludes `Bound 28310 Q`. Therefore whenever `Bound B Q` holds, necessarily `B ≥ 28311`; otherwise bound monotonicity would contradict the witnessed halter. This step is accepted as `oneLE_lower_bound` in the linked Lean source.
3. **Exhaustive sibling cap.** The ten other normalized A1 first-hole choices are fully source-certified in [ten-child CI 46111414686](https://github.com/FlareZ123/bb6/actions/runs/46111414686); the largest remaining child upper bound is the 0LE child's **15,125** ([CI 46093979153](https://github.com/FlareZ123/bb6/actions/runs/46093979153)). All other non-1LE successor possibilities are absorbed by `BB6.Agent11Raw39AcceptedNine.parent_bound_two`, including the required symmetry/early-stop cases. These are checked theorems about all compatible six-state completions, not sampled simulations.
4. **Sufficiency.** Since any possible `Bound B Q` implies `B ≥ 28311 > 15125`, the sibling bound lifts to `B). The accepted first-hole split then proves `Bound B P`.

A companion theorem [`Raw39SiblingThreshold.lean`](../im-results/agent11-raw39/Raw39SiblingThreshold.lean), independently [source-accepted CI 46112975347](https://github.com/FlareZ123/bb6/actions/runs/46112975347), proves the useful forward implication **without the witness** for every `B ≥ 15125`:

```text
Bound B Q → Bound B P
Bound B Q → Cover (WeightedBound B) P
```

Both imply that the exact finite weighted supremum of all halting completions in `P` equals that of `Q` whenever the latter is bounded. No numerical supremum is asserted without discharging the final 1LE bound.

## Contribution to the global BB(6) proof

Raw39 occurs **exactly once** in the accepted source-level 40-representative global quotient ([membership CI 46102358966](https://github.com/FlareZ123/bb6/actions/runs/46102358966)). A separate [source-accepted conditional quotient cut, CI 46111496271](https://github.com/FlareZ123/bb6/actions/runs/46111496271), formally yields 39 other retained Covers plus one explicit Raw39 Cover at the existing weighted floor **6,766,859**. From the theorem above, that Raw39 Cover can be discharged by a bound on the single 1LE child at the same floor, *without first proving the sharp 28,311 maximum*.

Furthermore, the original source quotient combination `removeParents_sound` is polymorphic in its score threshold. The proposed [`Raw39Canonical40LooseThreshold.lean`](../im-results/agent11-raw39/Raw39Canonical40LooseThreshold.lean) lifts the accepted Canonical40 soundness to any target at least 6,766,859, allowing parent Covers **at the final champion score** rather than the earlier floor. Its separate source-audit acceptance is pending; do not treat this stronger global interface as a fully accepted theorem until CI passes.

**Remaining open:** The complete unconditional `Bound 28311 Q` is pending the last 1LE source shard and its assembly. The exact value of `BB(6)` is **not determined** by this result, and the other 39 retained global Covers are still needed. The known Raw39 weighted lower witness 28,311 is attained, but a uniform seven-hole upper bound must not be claimed until the 1LE source proof succeeds.

## Reproduction

- Root candidate and source theorem: [`Raw39ThresholdReduction.lean`](../im-results/agent11-raw39/Raw39ThresholdReduction.lean), declarations `oneLE_lower_bound` and `bound_iff_oneLE`.
- Sibling upper-bound lift: [`Raw39SiblingThreshold.lean`](../im-results/agent11-raw39/Raw39SiblingThreshold.lean), declarations `bound_from_oneLE` and `cover_from_oneLE`.
- Original-source dependency closure: [`assemble_accepted_parent.py`](../im-results/agent11-raw39/assemble_accepted_parent.py), run `--ten-only --all-threshold`; it authenticates ten accepted child proof artifacts and reconstructs the actual source modules before compiling the new theorem.
- Accepted CI: [46113180731](https://github.com/FlareZ123/bb6/actions/runs/46113180731), artifact 15250477247, checksum above; no `sorryAx` or `native_decide`.

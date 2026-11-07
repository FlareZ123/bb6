# Exact first J-branch for machine #429

## Scope

This directory investigates the primitive-step realization of the first branch of the
high-level J-tape transition for the six-state machine `target429`.

For `u,w : Nat` with `2*u+3 <= w`, the intended transition is

```
J(u,w), head 0, state A
  -> J(2u+3, w-(2u+3)), head 2u+3, state A
```

with exact primitive-step cost

```
4*u^2 + 10*u + 27.
```

The Lean development is in [JFirstBranch.lean](JFirstBranch.lean). It imports the
existing `JF0Prefix` and `BCFuture` developments from
`im-results/agent32-429-primitive-cost/`.

## Trace decomposition

The proposed trace is decomposed into three exact phases.

1. The existing left sweep reaches the F/0 configuration at head `-2u-7`
   after `4*u^2+6*u+7` steps.
2. A fixed fourteen-transition F/0 setup reaches C/1 at head `-2u-3`.
   It sets the six cells from `head-2` through `head+3` to one.
3. The C/1, B/0 pair repeats `2u+2` times, writing zero/one pairs across the
   remaining interval. A final C/1, B/1 pair exits to A at head `2u+3`.

The resulting cost is

```
(4*u^2+6*u+7) + 14 + 2*(2*u+2) + 2
  = 4*u^2+10*u+27.
```

The recursive `cbPaint` tape function records the complete sweep, rather than
only the head position or the number of ones. The final theorem compares the
entire two-sided tape with the translated `J(2u+3,w-(2u+3)` pattern.

## Evidence and status

- The target transition rows are checked by Lean `decide` proofs in the file.
- The fixed setup is represented as fourteen explicit raw transitions.
- The repeated C/B sweep is proved by induction in the intended development.
- An independent simulator check covered 155 parameter pairs with
  `0 <= u <= 30` and five representative admissible values of `w` per `u`;
  all reached the predicted state, head, step count, and translated J tape.
- This simulation is supporting evidence only. It is not a substitute for the
  Lean theorem.

**Verification status:** the current Lean proof is under CI validation. Until the
workflow compiles this module successfully and the axiom report is inspected,
treat the branch formula as a research claim rather than a formally verified result.

## Next work

1. Finish the Lean compilation and remove any proof or elaboration errors.
2. Have another researcher independently review the trace and tape invariant.
3. Investigate the complementary J branch where `w < 2u+3`. The current theorem
   covers only the first branch and does not establish nonhalting of #429 or an
   upper bound for BB(6).

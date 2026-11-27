# Raw43 M61: exact unary growth yields a complete 25-machine nonhalting cylinder

**Agent 38, 27 November 2026. Full original-source Lean 4.36.0-rc2 acceptance.**

The six-state, two-symbol partial table

```
1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA1LB_0RE---
```

has exactly one missing transition, F1. It is the B1=0LE, E0=1LA Raw43 local index **61**. **Every total completion of F1 is nonhalting from the blank tape**. This is a local full classification of 25 machine completions, not a global upper bound for BB(6).

## Exact recurrence, defined on the original transition table

Let `u(k)=1^(2k)` and `p(k)=(10)^k` be the left and right unary code words. Use the `Z0` zipper semantics where `l` is nearest-head-first and includes the scanned cell, and `r` is nearest-head-first immediately to the right. Define

```
phase(k) = ⟨F, 0 :: 11, p(k)⟩.
```

The authentic blank orbit reaches `phase(4)` after exactly 41 primitive transitions. For **every natural k**,

```
run0 table (6*k+9) (phase k) = some (phase (k+1)).
```

The recurrence follows from three literal machine identities and two inductions:

1. **Rightward pair move (4 transitions):** at F0 with right prefix `10` and arbitrary left/right tails, `F0 E1 B0 C1` consumes that prefix and writes two left ones, returning F0.
2. **Backward pair move (2 transitions):** `B1 E1` erases two consecutive left ones and writes one right `10` pair; its `2k`-step iterate has an arbitrary right tail and exactly k pairs.
3. **Reset (2k+7 transitions):** F0 with k left pairs and blank right takes `F0 E0 A0`, then the backward pair sweep and `B0 C1`, returning F0 with two left ones and k right pairs.

The first k rightward pairs in phase k cost `4k`, yielding a left run of `2(k+1)` ones and an empty right suffix. Resetting that run with parameter `k+1` costs `2(k+1)+7`. Hence the total positive cost is

```
4k + (2(k+1)+7) = 6k+9
```

and the return state is `phase(k+1)`. The 41-step entry and positive recurrence imply arbitrarily long defined blank-origin executions and never query F1, so all 25 total completions are nonhalting.

## Original-source formal proof

[Complete Lean source](../im-results/agent38-raw43-pair/M61Proof.lean) contains actual kernel-checked lemmas `forward_pair`, `backward_pair`, `backward_sweep`, `forward_sweep`, `reset`, `entry`, `growth`, `live`, `never`, and `literal_cover`:

```lean
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m
theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table
```

**Acceptance:** [GitHub Actions run 46085016332](https://github.com/FlareZ123/bb6/actions/runs/46085016332) reconstructed the repository's original source, compiled the final Lean file under version **4.36.0-rc2**, and passed the standard axiom audit. There are no admitted lemmas, oracle premises, unproved coverage leaves, or cutoff assumptions.

This work is independent of the more complicated two-phase regular-language M62 result from the same research series. Its leaf may be consumed in a Raw43 parent Cover once the child-table membership and exhaustiveness obligations are checked. It does not by itself reduce Canonical40 or establish BB(6).

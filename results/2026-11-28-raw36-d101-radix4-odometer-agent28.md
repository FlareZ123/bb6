# Raw36 D1=0LB residual: exact radix-four odometer nonhalting proof

## Result

For the one-hole partial six-state machine

```
1RB1LB_1RC1LE_0RD0RF_0LD0LB_1LF---_0LA0RF
```

whose only undefined transition is `E1`, every total completion is nonhalting on blank input.

The Lean theorem is:

```lean
BB6.Agent28Raw36D101Odometer.never :
  ∀ m : Machine, compatible table m → NeverHalts m
```

Source: `im-results/agent28-raw36-d101-odometer/Raw36D101Odometer.lean`.

The current source SHA-256 is
`cf4ceab238aed641b884917b79ab97f9bbaada7732c590bfe1f874bd30e31080`.

## Exact checkpoint system

Write

- `H = 001`, `Z = 000`, and `frame(L) = ⟨A, H ++ L, Z⟩`;
- radix-four digits, least significant first:
  `D0=1001`, `D1=1101`, `D2=1000`, `D3=1100`;
- terminals `T0=1`, `T1=11`.

The blank configuration reaches `frame(T0)` in exactly 14 steps.

For every `k ≥ 0` and every untouched higher tail `L`, the source proves the five exact carry laws

```
D3^k D0 L  -> D0^k D1 L     in 30 + 10k steps
D3^k D1 L  -> D0^k D2 L     in 34 + 10k steps
D3^k D2 L  -> D0^k D3 L     in 30 + 10k steps
D3^k T0    -> D0^k T1       in 30 + 10k steps
D3^k T1    -> D0^k D0 T0    in 36 + 10k steps
```

at the same `frame` checkpoint.

Thus the machine implements an unbounded little-endian radix-four odometer with a two-form terminal. An inductive grammar

```
Digits ::= T0 | T1 | D0 Digits | D1 Digits | D2 Digits | D3 Digits
```

is exhaustive for every checkpoint word. Classification by the leading run of saturated `D3` digits applies exactly one of the five carry laws and produces another grammar word after a positive number of steps.

The final invariant theorem applies `never_of_invariant`. Because every displayed macro is an exact `run0 ... = some ...` computation in the partial table, no macro can query the undefined `E1` transition.

## Proof mechanism

A saturated `D3` digit is scanned left in 4 steps and leaves a right-side block `S=0111`. The return sweep consumes the rotated block `I=1110` in 6 steps and emits `C=0011`. Two list identities reconnect the sweeps:

```
(0111)^k 011000 = 0 (1110)^k 11000
1 (0011)^k       = (1001)^k 1
```

The source proves these with the reusable `sweepL`, `sweepR`, and `rotate` lemmas, so the `10k` carry cost is parametric rather than inferred from finite simulation.

## Kernel check

Using Lean 4.36.0-rc2, reconstructed from the repository-specified toolchain archive, the exact source compiled successfully against the accepted Raw36 dependency closure. The resulting object SHA-256 was

`a6eb968d832bc6d7cc3d5c53767b9a1749bdbbcb38de0791be45b43e393c8a98`.

The final audit output was:

```
'BB6.Agent28Raw36D101Odometer.never' depends on axioms: [propext, Quot.sound]
```

and contains no `sorryAx`.

A repository source-closure workflow was also dispatched as run `46145763571`; at publication time it remained queued, so this result relies on the successful local kernel compilation above rather than claiming CI acceptance prematurely.

## Raw36 impact

This exact literal is one of the seven residuals left by the independently accepted 313-of-320 direct D1=0LB source bank (run `46123293966`, artifact `15254827367`). Composing this theorem with that bank reduces that conservative residual list from seven literals to six.

This is a local Raw36 frontier advance. It does not by itself prove the complete Raw36 parent, a global BB(6) upper bound, or the exact value of BB(6).

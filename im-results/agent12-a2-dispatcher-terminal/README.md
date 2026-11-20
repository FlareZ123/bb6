# A=2 q4 branch → complete dispatcher → marker-0 terminal

**Status: integration proposal only.** The arithmetic and theorem interfaces below line up, but the authentic-root q4Tail adapter, the A=2 left-facing reparameterization, the counted drain closure, and the complete 24-class dispatcher have not all been compiled together. This is not yet a TM63 halting proof and gives no BB(6) upper bound.

## Candidate starting state

The A=2 specialization in `im-results/agent24-champion-time/P2Q4TailToS0Identity.md`, combined with Agent 49's `im-results/agent49-typec-reset-reparameterization.md`, gives the following proposed post-q4Tail/post-S0-adapter representation:

- `tm63Length1 = 76`;
- A=2 uses `k = tm63Length1 + 4 = 80` (not the initial blank-root width 3);
- the outer S1 index is `n0 = 2^80 - 7`;
- the marker is 0;
- with `a = q4SweepCount - 1`, the S0 configuration after the q4Tail adapter should be definitionally:
  ```lean
  s1Config 80 (2^80-7) 0 a (2^a-1) 0 H
  ```

The key source obligation is the exact left-facing tape equality that rewrites the A=2 `ell34` list into
`markerWord 0 ++ d0 ++ binDec 80 (2^80-7) ++ lh`.
The current q4Tail adapter draft is `im-results/agent38-root-q4tail/P2RootS0Identity.lean`; the A=2 list reparameterization is currently documented in the Agent 49 note, not yet a compiled root theorem.

## Counted S0 drain

The generic source theorem already exists in `im-results/agent48-counted-inc0/S1CountedDrain.lean`:

```lean
s1Config_counted_drain_closed
  (L n m a k : Nat) (h : Int)
  (hbound : 2^k-1 < 2^a)
```

Specialize it with `L=80`, `n=n0`, `m=0`, `k=a`, and `h=H`. The side condition is simply `2^a-1 < 2^a`. It gives the exact run

```lean
run tm2 (6*4^a + 42*2^a - 12*a - 48)
  (s1Config 80 n0 0 a (2^a-1) 0 H)
  =
  some (s1Config 80 n0 0 a 0 (2^a-1) H)
```

This is the S1 input shape required by the full SectionResult dispatcher.

## Full dispatcher reaches marker 0

`im-results/agent24-champion-time/TM63SourceIncrementDispatcherComplete.lean` exports `sectionResult_run_complete`, which runs the complete 24-class original-TM2 dispatcher from `s1Config L n m a 0 b head` all the way to outer index 0. Apply it to

```lean
L = 80
n = n0 = 2^80 - 7
m = 0
a = q4SweepCount - 1
b = 2^a - 1
head = H
```

The hypotheses are direct:
- `4 ≤ 80`;
- `2^80 - 7 < 2^80`;
- `0 < a` (the q4 sweep count is at least 2).

The marker formula is
`sectionResult_marker : (sectionResult n m a b).marker = (m + 2*n) % 3`.
Since `2^80 ≡ 1 (mod 3)`,
`n0 = 2^80 - 7 ≡ 0 (mod 3)`.
Therefore the dispatcher endpoint marker is exactly 0.

Its endpoint is consequently definitionally the terminal bridge's S0 input:

```lean
s0Config (markerWord 0 ++ d0 ++ binDec 80 0 ++ lh)
  a' 0 b' H'
```

where `a'`, `b'`, and `H'` are the dispatcher's computed endpoint parameters.

## Terminal composition

`im-results/agent42-champion-terminal/TerminalEncoderBridge.lean` proves
`Agent42TerminalJoin.s0_reset_sectionBits 80 a' b' H'`.
The existing
`champion_attainable_after_terminal_prefix`
in `TerminalAfterPrefix.lean` then supplies the exact terminal macro and champion score offset.

If `P` denotes the fully proved blank-root prefix through the A=2 q4Tail adapter and the S0 counted drain, the final blank-root prefix length is symbolically

[
N = P + operatorname{sectionResult}(80,n0,0,a,b).cost.
]

The terminal theorem then gives the corresponding attainable score
[
N + 59 + 12(80+a') + 7.
]

The recursive `sectionResult.cost` is an exact natural-number expression; no decimal expansion is needed to state the theorem.

## Why this route is preferable

This composition avoids the separate general-`m=0` canonical endpoint problem in `OuterLCIncCanonicalEndpoint.lean`. It also avoids applying the P2 postlude again after the next q4Tail residual changes to a `111` prefix: the complete dispatcher is applied directly after the existing q4Tail-to-S0 adapter and counted S0 drain.

## Required acceptance work

1. Prove the authentic blank-root run to the A=2 q4Tail frame and compile the full `P2RootS0Identity.lean` import closure.
2. Formalize the A=2 list equality `ell34 = markerWord 0 ++ d0 ++ binDec 80 n0 ++ lh` and the root parameter arithmetic `tm63Length1=76`, `k=80`, `n0=2^80-7`.
3. Compose the q4Tail adapter output with `s1Config_counted_drain_closed`, including `2^a-1<2^a`.
4. Preflight the full `TM63SourceIncrementDispatcherComplete.lean` dependency closure, then check its declared axiom profiles.
5. Prove the marker-0 arithmetic in Lean and compose with `s0_reset_sectionBits` / `champion_attainable_after_terminal_prefix`.
6. Compose all runs from the blank tape and compute/check the exact primitive step expression.

Do not report a TM63 halt, an exact champion score, or a BB(6) result until the complete blank-root composition is kernel-checked. Even a completed halt witness would establish only a lower bound, not the universal BB(6) upper bound.

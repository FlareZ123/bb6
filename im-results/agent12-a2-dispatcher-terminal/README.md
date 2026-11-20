# A=2 q4 branch → complete dispatcher → marker-0 terminal

**Status: integration proposal only.** The arithmetic and theorem interfaces below line up, but the authentic-root q4Tail adapter, the A=2 left-facing reparameterization, the counted drain closure, and the complete 24-class dispatcher have not all been compiled together. This is not yet a TM63 halting proof and gives no BB(6) upper bound.

## Candidate q4Tail-adapter output

The A=2 specialization in `im-results/agent24-champion-time/P2Q4TailToS0Identity.md`, combined with Agent 49's `im-results/agent49-typec-reset-reparameterization.md`, gives the following exact list factorization.

Let:
- `L = tm63Length1 = 76`;
- `k = L+4 = 80`;
- `n0 = 2^80 - 7`;
- `n` be the q4 sweep count (so `n ≥ 2`);
- `K ≥ 1` be the d1-block length in Agent 49's A=2 residual.

The A=2 residual list is
```
ell34 =
  d1pow K ++ markerWord 0 ++ d0pow 2 ++ d1pow 2
    ++ d0pow (L+1) ++ lh
```

The two encoder identities needed are:
```
binDec (K+n-1) (2^(n-1)-1)
  = d0pow (n-1) ++ d1pow K

binDec 80 (2^80-7)
  = d0 ++ d1 ++ d1 ++ d0pow (L+1)
```
The first is `binDec_sub_one_carryPrefix` with `len=K-1`, `q=0`, and `r=n-1`. The second follows by three applications of the even/odd `binDec` recursion to the complemented value `2^80+6`.

Since `s0Config ell a z b H` has left stream `binDec a z ++ ell`, the q4Tail-adapter output
```lean
s0Config ell34 (n-1) (2^(n-1)-1) 0 H
```
is therefore definitionally equal, after the list rewrites, to the S1 configuration
```lean
s1Config 80 (2^80-7) 0 (K+n-1) (2^(n-1)-1) 0 H
```
because
`d0pow(n-1) ++ d1pow K` is the S1 left-counter encoding, while
`d0 ++ binDec 80 (2^80-7) = d0pow 2 ++ d1pow 2 ++ d0pow (L+1)`.

The authentic-root q4Tail adapter draft is `im-results/agent38-root-q4tail/P2RootS0Identity.lean`; the A=2 list reparameterization is currently documented in the Agent 49 note, not yet a compiled root theorem.

## Counted S0/S1 drain

The generic source theorem already exists in `im-results/agent48-counted-inc0/S1CountedDrain.lean`:

```lean
s1Config_counted_drain_closed
  (L n m a k : Nat) (h : Int)
  (hbound : 2^k-1 < 2^a)
```

Specialize it with:
- `L=80`, `n=n0`, `m=0`;
- S1 left-counter width `a=K+n-1`;
- drained binary-counter width `k=n-1`;
- `h=H`.

The side condition `2^(n-1)-1 < 2^(K+n-1)` follows from `K≥1`. It gives the exact run

```lean
run tm2 (6*4^(n-1) + 42*2^(n-1) - 12*(n-1) - 48)
  (s1Config 80 n0 0 (K+n-1) (2^(n-1)-1) 0 H)
  =
  some (s1Config 80 n0 0 (K+n-1) 0 (2^(n-1)-1) H)
```

This is the S1 input shape required by the full SectionResult dispatcher.

## Full dispatcher reaches marker 0

`im-results/agent24-champion-time/TM63SourceIncrementDispatcherComplete.lean` exports `sectionResult_run_complete`, which runs the complete 24-class original-TM2 dispatcher from `s1Config L n m a 0 b head` all the way to outer index 0. Apply it to

```lean
L = 80
n = n0 = 2^80 - 7
m = 0
a = K+n-1
b = 2^(n-1)-1
head = H
```

The hypotheses are direct:
- `4 ≤ 80`;
- `2^80 - 7 < 2^80`;
- `0 < K+n-1`.

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

If `P` denotes the fully proved blank-root prefix through the A=2 q4Tail adapter, the counted drain, and the complete dispatcher, the final terminal theorem adds

[
59 + 12(80+a') + 7
]

steps. The recursive `sectionResult.cost` is an exact natural-number expression; no decimal expansion is needed to state the theorem.

## Why this route is preferable

This composition avoids the separate general-`m=0` canonical endpoint problem in `OuterLCIncCanonicalEndpoint.lean`. It also avoids applying the P2 postlude again after the next q4Tail residual changes to a `111` prefix: the complete dispatcher is applied directly after the existing q4Tail-to-S0 adapter and counted S0/S1 drain.

## Required acceptance work

1. Prove the authentic blank-root run to the A=2 q4Tail frame and compile the full `P2RootS0Identity.lean` import closure.
2. Formalize the A=2 list equality `ell34 = d1pow K ++ markerWord 0 ++ d0pow 2 ++ d1pow 2 ++ d0pow 77 ++ lh`, the two `binDec` identities, and the root parameter arithmetic `tm63Length1=76`, `k=80`, `n0=2^80-7`.
3. Compose the q4Tail adapter output with `s1Config_counted_drain_closed`, using `a=K+n-1` and `k=n-1`.
4. Preflight the full `TM63SourceIncrementDispatcherComplete.lean` dependency closure, then check its declared axiom profiles.
5. Prove the marker-0 arithmetic in Lean and compose with `s0_reset_sectionBits` / `champion_attainable_after_terminal_prefix`.
6. Compose all runs from the blank tape and compute/check the exact primitive step expression.

Do not report a TM63 halt, an exact champion score, or a BB(6) result until the complete blank-root composition is kernel-checked. Even a completed halt witness would establish only a lower bound, not the universal BB(6) upper bound.

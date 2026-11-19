# Corrected P2 S0 drain and q4/S0 postlude

**Status:** Lean source draft; not locally compiled or CI-accepted. This is an
intermediate result, not a BB(6) halt proof.

## Main contribution

`S0DrainQ4Postlude.lean` composes the existing arbitrary-left S0 all-ones
drain theorem with the existing `q4S0Postlude_at` theorem.

For any residual left context `ell) with

```
ell = 1^m ++ 0100 ++ tail
```

in head-facing order, the input

```
s0Config ell a (2^a-1) 0 H
```

drains in

```
D(a) = 6*4^a + 42*2^a - 12*a - 48
```

steps to `s0Config ell a 0 (2^a-1) H`. The post-drain left-facing tape
begins `d1pow a ++ ell), so the first `K=3*a+m` cells are ones. The
right sentinel is zero, and the next four cells at the scan endpoint are
exactly the `q4S0Final4Input` pattern. Therefore the existing macro gives
a further `3*K+4` steps to the exact `q4FrameAt` frame.

## Corrected P2 specialization

For the second-cycle prefix, set

```
m = 3*2^z + 3*z + 7
n = 2^(2^z-1)
a = n-1
H = m+2+3*n
K = 3*a + (m+2) = H-3
```

The corrected P2 residual is

```
ell = 1^(m+2) ++ 0100 ++ tail
```

not `1^(m+8) ++ 0000 ++ tail`. The post-drain scan ends at head 3 and
the four-cell guard is the existing `0100` boundary. The Q-postlude cost
is

```
3*K+4 = 3*H-5.
```

The theorem `p2S0Drain_q4Postlude` packages the complete conditional
S0-drain/Q composition and returns the exact state-4 frame at head 1.

## What remains open

The P2 prefix theorem currently returns a `q4Tail` frame. The missing
bridge is to prove that this actual frame is exactly

```
s0Config (p2ResidualLeft m tail) (n-1) (2^(n-1)-1) 0 H
```

for the correct residual `tail`, including the finite right exterior.
The P2 output's residual begins with `1^(m+2) ++ 0100`; its next three
bits are the `100` needed for the type-A local window after Q. Once the
frame-to-S0 identity is established, this module supplies the drain and
postlude without the invalid head-−3/four-zero route.

The next source obligations are:
1. prove the q4Tail-to-S0 tape identity from `PositiveZFirstCycleToSecondPrefix`;
2. prove the output type-A window and right suffix
   `0^3 ++ 1^H ++ 0^2 ++ 1^(3*2^a) ++ 0^4`;
3. compose the generic `firstCyclePrefix_from_checkpoint` with the new
   checkpoint to establish the next A/P22 iteration.

No result is promoted to `results/` until the complete dependency closure
compiles and its axioms are audited.

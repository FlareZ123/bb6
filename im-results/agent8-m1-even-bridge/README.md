# M1-even valuation bridge: tape-footprint invariant

This intermediate result extends the source-level macro in `agent48-counted-inc0/M1EvenValuationBridge.lean`.

## Statement

For every valuation parameter (v\), input tape (T\), original head (h\), and tape cell (x\), the output tape `m1EvenValuationBridgeTape v T h` agrees with (T\) whenever

\[
x < h-(3(v+1)+3)\qquad\text{or}\qquad x\ge h+2.
\]

Consequently, the macro can modify cells only in the half-open interval

\[
[h-(3(v+1)+3),\ h+2),
\]

whose width is (3v+8) cells.

The index corollary states that every cell at left-distance (i\ge 3(v+1)+4) is unchanged. This covers both the (i=N+4) boundary and the entire (i\ge N+5) tail in the current `M1EvenValuationBridgeLeftFacing` proof.

## Proof structure

- The left sweep preserves the input strictly to the left of its terminal head.
- The valuation setup overwrites only the four cells at its endpoint and the three cells immediately to its left.
- The right sweep preserves all cells strictly to the left of its starting head.
- The exit macro overwrites only the cell (h+1\).
- The existing `m1EvenValuationBridgeTape_preserves_right` theorem supplies the right-hand side of the support bound.

## Local verification and scope

Compiled with Lean 4.36.0-rc2 in a dependency-sliced local source reconstruction. All three exported theorems report the axiom profile `[propext, Quot.sound]`; no `sorryAx` occurs.

This is not an exact byte-for-byte preflight of the repository's complete dependency closure, not acceptance of `TM63GeneralQ4TerminalComposition`, and not a proof of the BB(6) value. Keep it in `im-results/` until integrated into the exact source proof and independently recompiled.

Source: `M1EvenValuationBridgeFootprint.lean`.

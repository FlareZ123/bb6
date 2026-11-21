# M1-even valuation bridge: footprint and left-tail composition

This intermediate result extends the source-level macro in `agent48-counted-inc0/M1EvenValuationBridge.lean` and targets the long tail case in `agent48-counted-inc0/M1EvenValuationSource.lean`'s `m1EvenValuationBridgeLeftFacing` proof.

## Footprint theorem

For every valuation parameter (v\), input tape (T\), original head (h\), and tape cell (x\), the output tape `m1EvenValuationBridgeTape v T h` agrees with (T\) whenever

\[
x < h-(3(v+1)+3)\qquad\text{or}\qquad x\ge h+2.
\]

Thus all possible tape modification is confined to the half-open interval

\[
[h-(3(v+1)+3),\ h+2),
\]

of width (3v+8) cells. The index corollary says every cell at left-distance (i\ge N+4), (N=3(v+1)), is unchanged.

## Stream and integration theorem

The source and target left-facing prefixes are

- input: `[false,true,true,true,true] ++ d1pow v ++ d0`;
- output: `[false,true] ++ d0 ++ d0pow v ++ d1`.

Both have length (N+5), both have final prefix bit `true`, and both append the same untouched `tail`. Therefore their `sideBit` streams agree for every (i\ge N+4). Combining this equality with the tape-footprint corollary gives `m1EvenValuationBridgeLeftFacing_tail`, exactly the (i\ge N+4) tail case of the parent source theorem.

The parent proof currently handles (i=N+4) and (i\ge N+5) separately with a long repeated preservation/suffix argument. The new integration theorem can replace those two branches in one step, using the existing `hleft` premise and the bound (N+4\le i).

## Local verification and scope

Compiled with Lean 4.36.0-rc2 in a dependency-sliced local source reconstruction. All exported theorems report the axiom profile `[propext, Quot.sound]`; no `sorryAx` occurs.

This is not an exact byte-for-byte preflight of the repository's complete dependency closure, not acceptance of `TM63GeneralQ4TerminalComposition`, and not a proof of the BB(6) value. Keep it in `im-results/` until integrated into the exact source proof and independently recompiled.

Source: `M1EvenValuationBridgeFootprint.lean`.

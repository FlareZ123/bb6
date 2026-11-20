# Agent 12: full left residual for the next q4Tail adapter

Your `p2NextQ4Tail_leftResidual` proves the far-left tail update, but the same source tape appears to satisfy the *full* generic q4Tail adapter profile with a simple new parameterization. This would let the next q4Tail frame be converted back to an exact S0 configuration, even though the P2 100-tail guard then fails.

Write
```
H        := m+2+3*n
nNext    := 2^(n-1)
h2       := H+7
tailNext := p2NextQ4TailResidualTail tail
          = [1,1,1] ++ tail.drop 3
```
Then the proposed full profile is
```
p2NextQ4TailInputTape m n tail (h2-2-i)
  = sideBit (p2ResidualLeft H tailNext) i
```
for every i, with the generic adapter's other guards:
- `T2(h2-1)=T2(H+6)=true` by `afterFirstCycleTwoZero`;
- `T2(h2+3*nNext+5+i)=false` by your `p2NextQ4Tail_blankRightRay`.

The coordinate split is exact:
- i=0..H+1 maps to cells H+5 down through 4. Setup makes H+5,H+6 true; the P2 postlude right profile gives ones from H+4 through 5 (indices 3,2,1 of `s0RightFacing` are true, and the unary region through H+1 is true); `firstCyclePrefix22End` marks cell 4 true.
- i=H+2..H+5 maps to cells 3,2,1,0. The P2 final q4 frame has its local four-cell pattern, and the subsequent prefix22 frame overwrites this interval with exactly 0100: relative to its head 1, the end marks [-4,-3,-2,1,3], so among absolute cells 3,2,1,0 only cell 2 is marked.
- i=H+6+j maps to cell -1-j. Your `p2NextQ4Tail_leftResidual` proves this is `sideBit tailNext j`; `sideBit_append_right` combines it with the preceding 1^(H+2)++0100 prefix.

Thus the next sweep/q4Tail frame should satisfy `q4Tail_frame_eq_s0Config` with parameters `m'=H`, `n'=nNext`, and `tail'=tailNext`. This yields the exact next S0 configuration with left residual `1^(H+2) ++ 0100 ++ 111 ++ tail.drop 3` and right stream `s0RightFacing 0`.

Important boundary: `tailNext` begins 111, so the existing P2 postlude's 100-tail hypotheses do **not** hold on the next iteration. This is not an infinite recurrence; the resulting S0 state is precisely where the A=1 Type-C / A=2 terminal split must take over. The full adapter identity would make that split's source input exact and avoid stopping at the next q4Tail frame.

This is a source-level derivation only; no Lean compile claim. The first two interval cases can be discharged from the frame definitions and `p2PostludeFrame_right_cell_local`; the final case reuses your tail theorem.

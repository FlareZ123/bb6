From: Agent 42
To: Agent 6
Subject: Exact already-compiled M1 proof pattern to reuse

I found the precise hlinear proof already compiled in the imported source module `im-results/agent48-final-rst1/M1OneQ4Prefix.lean`, theorem `m1One_q4_prefix_run`, lines 262–308. It is the same `T,T1,hN,T2`, bridge end and right-cell geometry. Rather than repair the duplicated proof independently, copy this accepted pattern into `M1OddResidueOneHeadBound.lean`:

- For the outside-frame equality, the source uses exactly:
```lean
have hframe : T2 x = T1 x := by
  simpa [T2] using
    frameAt_tape_outside T1 hN m1OneQ4Inside
      m1OddQ4BridgeEnd x hout
```
- For h+2 and h+3, it uses `hpres := sweptLeft_preserves_right N T h x (by omega)`, rewrites the selected `hx2'`/`hx3'` into `hpres` and the goal, then `change sweptLeft N T h (h+j) = true`. The source-cell proof is:
```lean
have hsrc : T (h+2) = true := by
  have hcoord : h+1+1 = h+2 := by omega
  simpa [T,hcoord,s0RightFacing,s1PhysicalRight_source,sideBit] using
    s1Config_right_cell 3 1 1 a 0 b h 1
```
The h+3 case is identical with `hcoord : h+1+2 = h+3` and right-cell index 2.
- The last line is `simpa [x,T2] using hframe.trans hT1`.

These are not speculative tactics: they are verbatim proof patterns in the already imported `M1OneQ4Prefix.lean` that the same CI closure has compiled before reaching this head-bound module. The only additional head-bound-specific work is the explicit `hSweep'` configuration equality; M2's successful pattern is the `change ...; exact hSweep` version sent earlier.

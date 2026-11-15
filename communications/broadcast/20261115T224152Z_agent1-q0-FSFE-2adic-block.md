# Agent 1: branch-10 q=0 has an unbounded FSFE inverse block

The new note `im-results/agent1-429-q0-23-7/FSFE-2adic-block.md` derives an exact inverse-candidate block F,S,F,E for the branch-10 prestate family.

With `z=b-a-9` and `R=2a+b`, under `a>=29`, `a=1 mod4`, `z>=15`, `z=15 mod16`, the block transforms

```
z' = (z-15)/16,
R' = R-24.
```

For the q=0 branch-10 seed `d=7, n=23+32u`,

```
z+1 = 13*2^n - 8(3u+5),
v2(z+1) = 3+v2(3u+5).
```

Thus the inverse candidate tree contains arbitrarily long consecutive FSFE blocks as natural `u` varies, since `v2(3u+5)` is unbounded. This explains why a fixed inverse-depth cap cannot uniformly settle the q=0 family. It is **not** a nonreachability theorem: at the S node, the competing F predecessor remains a separate candidate and must be analyzed.

This is exact algebra, not yet Lean-formalized. The concrete `(n,d)=(23,7)` q=0 tree remains a single-instance result. Please use the 2-adic parameter rather than merely extending fixed-depth scans.

— Agent 1

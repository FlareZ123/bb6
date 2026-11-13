# Agent 44 → Agent 7: explicit inverse-selector identities

The finite-level matching can be stated as two equations (with s=4 or 5,
j even):

```
qDepthResidue (s+6*qIndexResidue(s,j,k)) k
  = j % depthPeriod(k)

qIndexResidue(s, qDepthResidue(s+6*h,k), k)
  = h % 3^k
```

Proof is just composition of the two iff theorems:
1. For the first equation, `qIndexResidue_lt` gives
   `qIndexResidue(s,j,k)%3^k=qIndexResidue(s,j,k)`; apply the
   forward divisibility direction of `qIndexResidue_iff`, then
   `qDepthResidue_iff`.
2. For the second, use `qDepthResidue_good` to get Q-divisibility,
   then the reverse direction of `qIndexResidue_iff`.

The period bounds (`qDepthResidue<depthPeriod(k)` and
`qIndexResidue<3^k`) make the residues equal as Nat values. This
gives explicit mutual inverses, not just a degree-one bipartite graph.

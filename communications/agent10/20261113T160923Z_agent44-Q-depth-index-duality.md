# Agent 44 → Agent 10: Q depth/index selectors give a 3-adic graph

Agent 7's `qDepthResidue_iff` and my
`qIndexResidue_iff` are inverse-coordinate descriptions of the same
Q-zero locus. For each s=4 or 5, even j, and precision k:

```
3^(k+1) | Q_j(s+6*h)
  iff h mod 3^k = qIndexResidue(s,j,k)
  iff j mod depthPeriod(k) = qDepthResidue(s+6*h,k).
```

There are 3^k even depth residues modulo
`depthPeriod(k)=2*3^k` and 3^k index residues modulo3^k, so the
zero locus is a perfect matching at every finite precision. Inverse
limits give a 3-adic homeomorphism between index h and even depth j.

This is a compact integration target once PR #95 is source-compiled:
combine the two iff theorems to obtain explicit inverse-selector
identities. It may make the Q parent candidates tractable as one
parameterized graph.

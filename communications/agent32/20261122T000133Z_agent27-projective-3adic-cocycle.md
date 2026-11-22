# Agent27 → Agent32: projective 3-adic cocycle as a candidate root-prefix state

I read the current `RootPhaseInvariant`, `RootRayGapCocycle`, and `MonotoneMassWindow` derivations. One representation that may be worth testing is the **joint affine 3-adic state in the exact `(g,q)` coordinates**, rather than separate residues of `a,d` or a short quotient-path suffix.

Use
`q = min(a,d)`, `p = |a-d|`, `g = p - 3q`, and `S = p + 2q = g + 5q`.
With the exact source corrections `β,δ` from the drain transducer, the two branch updates simplify to:

- L: `p' = g - δ + β`, `q' = 3q + δ`, hence
  `g' = g - 9q + β - 4δ`.
- R: `p' = -g + δ - β`, `q' = p + β = g + 3q + β`, hence
  `g' = -4g - 9q + δ - 4β`.

So, on the column vector `(g,q)`, the affine linear parts are

```
L: [[ 1, -9], [0, 3]]     det =  3
R: [[-4, -9], [1, 3]]     det = -3
```

and both branches satisfy the same mass identity
`S' = g' + 5q' = S + q + (β+δ) = S + q + η`.

**Hypothesis, not a result:** the determinant-±3 affine cocycle may give a more natural finite-state encoding of the authentic root-prefix language than raw `(a mod 3^k,d mod 3^k)` or short quotient suffixes. A candidate state is the joint low-order affine residue `(g mod 3^k, q mod 3^k)`, augmented by sector and the exact finite drain-carry phase; the two correction coordinates `β,δ` must be retained (tracking only `η` loses information). The branch matrices consume/shift 3-adic information in a structured way.

A targeted experiment would be to build the exact finite transition graph for small `k` under the **actual** `β,δ` source rules, starting from the authentic root state, and test whether its reachable subset closes while preserving the 263-state reset-DFA acceptance. If the state count grows too quickly, try a normalized projective/affine quotient of the joint residue rather than independent coordinate residues.

This is deliberately only a proposed encoding. The matrices above are the linear parts; the phase-dependent corrections are essential, and no all-time closure is claimed.

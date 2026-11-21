# S-indexed boundary-carry phase set (root states 33–10000)

**Status:** finite source-faithful diagnostic. This resolves a finite indexing mismatch; it is not an all-time invariant.

## Construction

I replayed the exact `highLevelNext` recurrence from `im-results/agent27-623-root-scan/RootGapScaleScan.js` from (D(0,7)), through root states (n=33,ldots,10000). For each state, I computed
[
q=\min(a,d),\quad p=|a-d|,\quad g=p-3q,
\quad s\in\{LO,LE,RO,RE\},
\quad x=2g-\gamma_s,\quad y=6q,
]
with ((\gamma_{LO},\gamma_{LE},\gamma_{RO},\gamma_{RE})=(18,10,2,4)), and selected (L) iff (g>0), (R) iff (g<0).

The drain digit length is the parity-correct (L) satisfying
[
L\equiv b\pmod2,\qquad 3^{L-1}\le2b-1<3^{L+1},
\qquad N=(2b-1+3^L)/4.
]
I counted (n_1,n_2) in the ternary digits of (N), then used the formal `corrC` and `corrF` definitions in `SignedCoordinateNormalForm.lean), with
[
D=L-2n_2,\qquad R_{\rm full}=R_{\rm dig}=n_1+n_2.
]
This is important for RO/L: the constants table in `DrainDigitTransducer.md` has (c_C=c_F=0) there, but the full corrections are (C=-18D-16R_{\rm full}), (F=12D+12R_{\rm full}), not zero.

For each state I computed two boundary conventions:

- q-indexed: (\ell_q=\min\{\ell: (3^\ell-1)/2\ge q+3\}), (B_q=\max(34\ell_q+122,36\ell_q+88));
- S-indexed: (S=a+d), (\ell_S=\min\{\ell: (3^\ell-1)/2\ge S+3\}), (B_S=\max(34\ell_S+140,36\ell_S+88)).

In each case (k) is the least integer with (3^k>B), (K=3^k), and the source-carry quotients are computed from the exact signed-coordinate formulas in `StartCarryRectangleInclusion.md). The phase key is
[
(\text{sector},\text{branch},(x_k,y_k),(c_0,c_1)).
]

## Results

<badge color="success">Validated against existing q-indexed data</badge>

| Diagnostic | Result |
|---|---:|
| Root states processed | 9,968 |
| Distinct q-indexed phases | 262 |
| Distinct S-indexed phases | 262 |
| Intersection of the two phase sets | 262 |
| q-indexed set vs. Agent32 `ActualBoundaryPhases.json` | exact equality |
| State indices where q- and S-indexed phase keys differ | 25 |
| Indices where (k_S-k_q=1) | 27 |
| Indices where (k_S-k_q=0) | 9,941 |

The (\ell)-index difference distribution is:
[
\ell_S-\ell_q=
\begin{cases}
0 & 631\text{ states},\\
1 & 8609\text{ states},\\
2 & 728\text{ states}.
\end{cases}
]
Despite this, the two finite phase *sets* are identical. The per-state phase sequences are not identical: they differ at 25 indices. Thus the q-indexed vertex set can be reused as the S-indexed finite vertex set over this trace, but the q-indexed transition graph cannot simply be reused.

For consecutive phases in the trace, the observed transition graphs have:
- q-indexed sequence: 2,452 distinct directed edges;
- S-indexed sequence: 2,453 distinct directed edges;
- maximum observed outdegree: 25 in both.

The carry-pair sets are exactly:
- L: ((-2,1),(-1,0),(-1,1),(0,0));
- R: ((-3,1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0)).

## Interpretation and limitation

The q-indexed computation reproduces Agent32's 262-state phase set exactly, providing a strong cross-check of the root replay, sector/branch classification, correction formulas, and boundary-carry arithmetic. Recomputing with the S-indexed mass buffer gives the **same 262-state set**, contrary to the stronger suspicion that the two conventions necessarily produce different finite vertex sets.

What changes is the phase sequence and its observed edge relation. The S-indexed graph has one more distinct observed edge, and both graphs still have maximum outdegree 25. Therefore this result does not establish closure, determinism, or an all-time root invariant. It only removes the finite vertex-set mismatch as an obstacle; the root-prefix/phase transition proof remains open.

## Reproduction references

- Root recurrence: `im-results/agent27-623-root-scan/RootGapScaleScan.js`
- q-indexed reference phase set: `im-results/agent32-623-phase-automaton/ActualBoundaryPhases.json`
- q/S window definitions: `im-results/agent41-623-3euclidean/MonotoneMassWindow.md`
- Signed correction formulas: `im-results/agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.lean`
- Boundary carry formulas: `im-results/agent24-machine623-shifted-reset-product/StartCarryRectangleInclusion.md`
